const SUITS=["S","D","H","C"];
const RED_SEQUENCE_VP=2;
const SOLO_SUPREMACY_THRESHOLD=4;
const SOLO_WIN_THRESHOLD=10;
const SUIT_NAME={S:"♠",D:"♦",H:"♥",C:"♣"};
const SUIT_ICON={S:"♠",D:"♦",H:"♥",C:"♣"};
const RANKS=["A","2","3","4","5","6","7","8","9","10","J","Q","K"];
const RANK_VAL=Object.fromEntries(RANKS.map((r,i)=>[r,i+1]));
const MASK13=(1<<13)-1;
const TABLEAU_MODEL={
  ancient:[
    {faceDown:false,xs:[2,3,4]},
    {faceDown:true,xs:[1.5,2.5,3.5,4.5]},
    {faceDown:false,xs:[1,2,3,4,5]},
    {faceDown:true,xs:[0.5,1.5,2.5,3.5,4.5,5.5]},
    {faceDown:false,xs:[0,1,2,3,4,5,6]}
  ],
  modern:[
    {faceDown:true,xs:[2.5,3.5]},
    {faceDown:false,xs:[2,3,4]},
    {faceDown:true,xs:[1.5,2.5,3.5,4.5]},
    {faceDown:false,xs:[1,2,3,4,5]},
    {faceDown:true,xs:[0.5,1.5,2.5,3.5,4.5,5.5]},
    {faceDown:false,xs:[0,1,2,3,4,5,6]}
  ]
};
let G=null;
let aiTimer=null;
let renderScheduled=false;
const SOLO_MODE=true;
const SOLO_NON_HUMAN_PLAYER_INDEX=1;
const SOLO_JOKER_ENABLED=false;

const AI_BASE_BUDGET_MS=5000;
const HEURISTIC_WEIGHT_FOOD=1.25;
const HEURISTIC_WEIGHT_DIAMOND=0.9;
const HEURISTIC_WEIGHT_TECH=0.9;

function makeFeat(){
  return {sw:0,cw:0,hMask:0,hAdj:0,dMask:0,dAdj:0};
}
function cloneFeat(feat){
  return {...feat};
}

function isSlotGone(slot){
  return !!(slot.removed || slot.pendingAIPick);
}

function countRemainingCards(tableau){
  let n=0;
  for(const sl of tableau.slots) if(!isSlotGone(sl)) n++;
  return n;
}
function getAiThinkingBudgetMs(state){
  const left=countRemainingCards(state.tableau);
  if(left<=6) return 6500;
  if(left<=10) return 5800;
  return AI_BASE_BUDGET_MS;
}

function scheduleRender(){
  if(renderScheduled) return;
  renderScheduled=true;
  requestAnimationFrame(()=>{
    renderScheduled=false;
    render();
  });
}

function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}
function makeDeck(){
  const cards=[]; let id=0;
  for(const s of SUITS){for(const r of RANKS){cards.push({id:id++,suit:s,rank:r});}}
  return cards;
}
function getAgeSlotCount(age){
  return TABLEAU_MODEL[age].reduce((total,row)=>total+row.xs.length,0);
}
function splitDeckForAges(deck){
  const shuffled=shuffle(deck.slice());
  const ancientCount=getAgeSlotCount("ancient");
  const modernCount=getAgeSlotCount("modern");
  const ancient=shuffled.slice(0,ancientCount);
  const modern=shuffled.slice(ancientCount,ancientCount+modernCount);
  return {ancient:shuffle(ancient),modern:shuffle(modern)};
}
function makeUnknownModernDeck(){
  return shuffle(makeDeck()).slice(0,getAgeSlotCount("modern"));
}
function label(c){return `${c.rank}${SUIT_ICON[c.suit]}`;}
function cardClass(c){return `suit${c.suit}`;}
function sortCardsByRank(cards){
  return cards.slice().sort((a,b)=>RANK_VAL[a.rank]-RANK_VAL[b.rank]);
}
function groupStraightRuns(cards){
  const sorted=sortCardsByRank(cards);
  if(!sorted.length) return [];
  const groups=[[sorted[0]]];
  for(let i=1;i<sorted.length;i++){
    const prev=groups[groups.length-1][groups[groups.length-1].length-1];
    const cur=sorted[i];
    if(RANK_VAL[cur.rank]===RANK_VAL[prev.rank]+1) groups[groups.length-1].push(cur);
    else groups.push([cur]);
  }
  return groups;
}
function suitMaximalGroups(cards,suit){
  const cardByRank=new Map(cards.filter(c=>c.suit===suit).map(c=>[RANK_VAL[c.rank],c]));
  const owned=new Set(cardByRank.keys());
  if(owned.size<2) return [];
  const present=i=>owned.has(i===0?13:i===14?1:i);
  const groups=[];
  for(let i=1;i<=13;i++){
    if(!owned.has(i)) continue;
    if(present(i-1)) continue;
    const ranks=[i];
    let cur=i;
    while(present(cur+1)){
      cur=cur===13?1:cur+1;
      if(cur===i) break;
      ranks.push(cur);
    }
    if(ranks.length>=2) groups.push(ranks.map(r=>cardByRank.get(r)).filter(Boolean));
  }
  return groups;
}
function groupedSuitTokens(suit,cards){
  const sorted=sortCardsByRank(cards);
  if(suit==="H" || suit==="D"){
    const runs=suitMaximalGroups(sorted,suit);
    const used=new Set(runs.flat().map(c=>c.id));
    const singles=sorted.filter(c=>!used.has(c.id)).map(c=>({key:RANK_VAL[c.rank],cards:[c]}));
    const groups=runs.map(g=>({key:RANK_VAL[g[0].rank],cards:g}));
    return [...singles,...groups].sort((a,b)=>a.key-b.key);
  }
  return sorted.map(c=>({key:RANK_VAL[c.rank],cards:[c]}));
}

function layout(model){
  const w=64,h=90;
  const overlap=(110-42)*0.6; // riduce del 40% la sovrapposizione verticale precedente
  const v=h-overlap;
  const hStep=68;
  const allX=model.flatMap(r=>r.xs);
  const minX=Math.min(...allX), maxX=Math.max(...allX);
  const width=w+(maxX-minX)*hStep;
  const pos=[];
  let idx=0;
  for(let row=0;row<model.length;row++){
    for(let col=0;col<model[row].xs.length;col++){
      const gx=model[row].xs[col];
      pos[idx++]={row,col,gridX:gx,x:(gx-minX)*hStep,y:row*v};
    }
  }
  return {w,h,hStep,minX,pos,width,height:(model.length-1)*v+h};
}

function buildRows(model){
  let idx=0;
  return model.map((cfg,row)=>cfg.xs.map((gridX,col)=>({idx:idx++,row,col,gridX})));
}
function buildCovering(rows){
  const total=rows.reduce((a,r)=>a+r.length,0);
  const coveredBy=Array.from({length:total},()=>[]);
  for(let r=0;r<rows.length-1;r++){
    const upper=rows[r], lower=rows[r+1];
    const lowerByX=new Map(lower.map(s=>[s.gridX,s.idx]));
    for(const slot of upper){
      const c1=lowerByX.get(slot.gridX-0.5);
      const c2=lowerByX.get(slot.gridX+0.5);
      if(c1!==undefined) coveredBy[slot.idx].push(c1);
      if(c2!==undefined) coveredBy[slot.idx].push(c2);
    }
  }
  return coveredBy;
}
function buildCoveredBy(covering){
  const coveredBy=Array.from({length:covering.length},()=>[]);
  for(let i=0;i<covering.length;i++) for(const c of covering[i]) coveredBy[c].push(i);
  return coveredBy;
}
function buildTableau(age,deck){
  const model=TABLEAU_MODEL[age], geom=layout(model), slots=[];
  const rows=buildRows(model);
  const covering=buildCovering(rows);
  for(const p of geom.pos){
    const card=deck.pop();
    const faceDown=model[p.row].faceDown;
    slots.push({card,removed:false,pendingAIPick:false,faceDown,row:p.row,col:p.col,gridX:p.gridX,x:p.x,y:p.y});
  }
  return {slots,geom,coveredBy:covering,coveredByRev:buildCoveredBy(covering)};
}
function accessibility(tableau){
  const {slots,coveredBy}=tableau;
  return slots.map((s,i)=>{
    if(isSlotGone(s)) return false;
    return !(coveredBy[i]||[]).some(cIdx=>!isSlotGone(slots[cIdx]));
  });
}
function flipNew(slots,acc){
  let f=0;
  for(let i=0;i<slots.length;i++) if(!isSlotGone(slots[i]) && slots[i].faceDown && acc[i]){slots[i].faceDown=false; f++;}
  return f;
}

function commitPendingAIPicks(){
  if(!G?.pendingAIRemovals?.length) return;
  for(const idx of G.pendingAIRemovals){
    const slot=G.tableau.slots[idx];
    if(!slot || !slot.pendingAIPick) continue;
    slot.pendingAIPick=false;
    slot.removed=true;
  }
  G.pendingAIRemovals=[];
}
function bitOfRank(rank){ return 1<<(RANK_VAL[rank]-1); }
function popcount13(x){ x>>>=0; let c=0; while(x){ x&=x-1; c++; } return c; }
function diamondAdjFromMask(mask){
  mask&=MASK13;
  const rot=((mask<<1)&MASK13) | (mask>>>12);
  return popcount13(mask&rot);
}
function swordValue(card){
  const v=RANK_VAL[card.rank];
  return (v<=9) ? 1 : 2;
}
function foodPower(cards){
  return cards.filter(c=>c.suit==="C").reduce((a,c)=>a+swordValue(c),0);
}
function updateFeat(feat,card){
  if(card.suit==="S") feat.sw+=swordValue(card);
  if(card.suit==="C") feat.cw+=swordValue(card);
  if(card.suit==="H"){
    feat.hMask|=bitOfRank(card.rank);
    feat.hAdj=diamondAdjFromMask(feat.hMask);
  }
  if(card.suit==="D"){
    feat.dMask|=bitOfRank(card.rank);
    feat.dAdj=diamondAdjFromMask(feat.dMask);
  }
}
function swords(cards){
  return cards.filter(c=>c.suit==="S").reduce((a,c)=>a+swordValue(c),0);
}

function suitSequences(cards,suit){
  const owned=new Set(cards.filter(c=>c.suit===suit).map(c=>RANK_VAL[c.rank]));
  if(owned.size<2) return [];
  const present=i=>owned.has(i===0?13:i===14?1:i);
  if(owned.size===13) return [{length:13,high:13}];
  const seq=[];
  for(let i=1;i<=13;i++){
    if(!owned.has(i)) continue;
    if(present(i-1)) continue;
    let len=1,cur=i;
    while(present(cur+1)){len++;cur=cur===13?1:cur+1; if(cur===i) break;}
    if(len>=2){
      let high=i;
      for(let k=0,cc=i;k<len;k++){if(cc===13) high=13; else if(high!==13 && cc>high) high=cc; cc=cc===13?1:cc+1;}
      seq.push({length:len,high});
    }
  }
  return seq;
}

function countSoloRedSequences(cards,suit){
  return suitSequences(cards,suit).length;
}
function scoreSoloCards(cards){
  const hearts=countSoloRedSequences(cards,"H");
  const diamonds=countSoloRedSequences(cards,"D");
  const vp=RED_SEQUENCE_VP*(hearts+diamonds);
  return {
    vp,
    detail:{
      hearts,
      diamonds,
      heartVp:hearts*RED_SEQUENCE_VP,
      diamondVp:diamonds*RED_SEQUENCE_VP,
      totalSequences:hearts+diamonds
    }
  };
}
function scoreGame(){
  return scoreSoloCards(G.players[0].cards);
}
function checkSupremacy(){
  const f0=G.players[0].feat, f1=G.players[1].feat;
  const aiMilitaryDiff=f1.sw-f0.sw;
  if(aiMilitaryDiff>=SOLO_SUPREMACY_THRESHOLD) return {winner:1,reason:`♠ AI immediate victory (diff >=${SOLO_SUPREMACY_THRESHOLD})`};

  const aiFoodDiff=f1.cw-f0.cw;
  if(aiFoodDiff>=SOLO_SUPREMACY_THRESHOLD) return {winner:1,reason:`♣ AI immediate victory (diff >=${SOLO_SUPREMACY_THRESHOLD})`};

  return null;
}

function highValueBlackOpenMoves(open){
  return open.filter(i=>{
    const card=G.tableau.slots[i]?.card;
    return card && (card.suit==="S" || card.suit==="C") && swordValue(card)===2;
  });
}

function newGame(){
  const {ancient,modern}=splitDeckForAges(makeDeck());
  const first=0;
  G={
    age:"ancient", nextAgeFirst:1-first, current:first, ended:false,
    decks:{ancient,modern}, tableau:null,
    players:[
      {name:"You",cards:[],joker:SOLO_JOKER_ENABLED,isAI:false,feat:makeFeat()},
      {name:"AI",cards:[],joker:SOLO_JOKER_ENABLED,isAI:true,feat:makeFeat()}
    ],
    lastTaken:null, picksLeftThisTurn:1,
    pendingAIRemovals:[],
    awaitingRivalChoice:false,
    rivalChoiceIndices:[],
    rivalChoiceSuit:null,
    rivalChoiceReason:"",
    phaseTwoOpeningRivalPickPending:false
  };
  G.tableau=buildTableau("ancient",G.decks.ancient);
  log(`New game. ${G.players[G.current].name} starts.`);
  render();
}

function log(msg){
  const p=document.createElement("p"); p.className="line"; p.textContent=msg;
  const l=document.getElementById("log"); l.prepend(p);
}

function takeCard(idx){
  if(G.ended) return;
  const slots=G.tableau.slots, accBefore=accessibility(G.tableau);
  const s=slots[idx];
  if(!accBefore[idx]||s.faceDown||isSlotGone(s)) return;

  const pl=G.players[G.current];
  if(!pl.isAI && G.pendingAIRemovals.length) commitPendingAIPicks();

  if(pl.isAI){
    s.pendingAIPick=true;
    if(!G.pendingAIRemovals.includes(idx)) G.pendingAIRemovals.push(idx);
  }else{
    s.removed=true;
  }

  pl.cards.push(s.card);
  updateFeat(pl.feat,s.card);
  G.lastTaken={player:G.current,card:s.card};

  G.picksLeftThisTurn=Math.max(0,G.picksLeftThisTurn-1);
  const accAfter=accessibility(G.tableau);
  const f=flipNew(slots,accAfter);
  log(`${pl.name} takes ${label(s.card)}.${f?` Reveals ${f} cards.`:""}`);

  const sup=checkSupremacy();
  if(sup){
    G.ended=true;
    log(`🏆 ${G.players[sup.winner].name} wins by ${sup.reason}.`);
    showSupremacyModal(sup);
    render();
    return;
  }

  if(!pl.isAI && G.picksLeftThisTurn<=0){
    startRivalSelection();
    return;
  }
  endTurnOrAge();
}

function resolveRivalChoice(idx){
  if(!G?.awaitingRivalChoice) return;
  if(!G.rivalChoiceIndices.includes(idx)) return;
  const slot=G.tableau.slots[idx];
  if(!slot || slot.faceDown || isSlotGone(slot)) return;
  slot.removed=true;
  const ai=G.players[1];
  ai.cards.push(slot.card);
  updateFeat(ai.feat,slot.card);
  log(`AI takes ${label(slot.card)} (${G.rivalChoiceReason}).`);
  G.lastTaken={player:1,card:slot.card};

  // In solo mode, rival picks are usually a consequence of the human move
  // (the pick was already consumed). The exception is the Phase 2 opening
  // when AI starts and this rival pick is the AI turn action itself.
  if(G.players[G.current]?.isAI){
    G.picksLeftThisTurn=Math.max(0,G.picksLeftThisTurn-1);
  }

  G.awaitingRivalChoice=false;
  G.rivalChoiceIndices=[];
  G.rivalChoiceSuit=null;
  G.rivalChoiceReason="";
  const accAfter=accessibility(G.tableau);
  const f=flipNew(G.tableau.slots,accAfter);
  if(f) log(`Reveals ${f} cards.`);
  const sup=checkSupremacy();
  if(sup){
    G.ended=true;
    log(`🏆 ${G.players[sup.winner].name} wins by ${sup.reason}.`);
    showSupremacyModal(sup);
    render();
    return;
  }
  endTurnOrAge();
}

function startRivalSelection(){
  const open=legalOpenMoves(G.tableau);
  if(G.phaseTwoOpeningRivalPickPending){
    G.phaseTwoOpeningRivalPickPending=false;
    if(open.length===0){
      log("AI has no legal card to take.");
      endTurnOrAge();
      return;
    }
    const blackHighValue=highValueBlackOpenMoves(open);
    if(blackHighValue.length===1){
      G.awaitingRivalChoice=true;
      G.rivalChoiceIndices=blackHighValue;
      G.rivalChoiceReason="phase 2 opening pick: black 2-point card (forced priority)";
      resolveRivalChoice(blackHighValue[0]);
      return;
    }
    if(blackHighValue.length>1){
      G.awaitingRivalChoice=true;
      G.rivalChoiceIndices=blackHighValue;
      G.rivalChoiceReason="phase 2 opening pick: choose a black 2-point card for AI";
      log("Phase 2 opening AI pick: choose a black 2-point card (10/J/Q/K of ♠ or ♣).");
      render();
      return;
    }
    G.awaitingRivalChoice=true;
    G.rivalChoiceIndices=leftmostRightmostOpenMoves(open);
    G.rivalChoiceReason="phase 2 opening pick: choose leftmost or rightmost unlocked card for AI";
    if(G.rivalChoiceIndices.length===1){
      resolveRivalChoice(G.rivalChoiceIndices[0]);
      return;
    }
    log("Phase 2 opening AI pick: choose leftmost or rightmost unlocked card.");
    render();
    return;
  }
  if(open.length===0){
    log("AI has no legal card to take.");
    endTurnOrAge();
    return;
  }
  if(open.length===1){
    G.awaitingRivalChoice=true;
    G.rivalChoiceIndices=open.slice();
    G.rivalChoiceReason="single unlocked card (forced)";
    resolveRivalChoice(open[0]);
    return;
  }
  G.awaitingRivalChoice=true;
  const blackHighValue=highValueBlackOpenMoves(open);
  if(blackHighValue.length===1){
    G.rivalChoiceIndices=blackHighValue;
    G.rivalChoiceReason="black 2-point card (forced priority)";
    resolveRivalChoice(blackHighValue[0]);
    return;
  }
  if(blackHighValue.length>1){
    G.rivalChoiceIndices=blackHighValue;
    G.rivalChoiceReason="choose a black 2-point card for AI";
    log("Choose AI card: it must be a black 2-point card (10/J/Q/K of ♠ or ♣).");
    render();
    return;
  }
  G.rivalChoiceIndices=leftmostRightmostOpenMoves(open);
  G.rivalChoiceReason="choose leftmost or rightmost unlocked card for AI";
  if(G.rivalChoiceIndices.length===1){
    resolveRivalChoice(G.rivalChoiceIndices[0]);
    return;
  }
  log("Choose AI card: leftmost or rightmost unlocked card.");
  render();
}

function onHumanCardClick(idx){
  if(!G || G.ended) return;
  if(G.awaitingRivalChoice){
    resolveRivalChoice(idx);
    return;
  }
  if(G.players[G.current].isAI) return;
  takeCard(idx);
}

function canUseJokerDouble(player=G.current){
  return !G.ended && G.current===player && G.players[player].joker && G.picksLeftThisTurn===1;
}
function useJokerDouble(player=G.current){
  if(!canUseJokerDouble(player)) return false;
  G.players[player].joker=false;
  G.picksLeftThisTurn=2;
  log(`${G.players[player].name} builds Wonder (Extra Turn): 2 picks this turn.`);
  return true;
}

function showEndgameModal(sc,winner){
  const d=document.getElementById("modal");
  d.classList.remove("modernSwapModal");
  const targetMet=sc.vp>=SOLO_WIN_THRESHOLD;
  d.innerHTML=`
    <h3>Game Over</h3>
    <p>Solo target score summary:</p>
    <table class='endSummary'>
      <thead>
        <tr><th>Category</th><th>You</th></tr>
      </thead>
      <tbody>
        <tr><td>♥ Sequences</td><td><strong>${sc.detail.hearts}</strong> (${sc.detail.heartVp} VP)</td></tr>
        <tr><td>♦ Sequences</td><td><strong>${sc.detail.diamonds}</strong> (${sc.detail.diamondVp} VP)</td></tr>
        <tr><td>Total red sequences</td><td><strong>${sc.detail.totalSequences}</strong></td></tr>
      </tbody>
      <tfoot>
        <tr class='tot'><td>Total VP</td><td><strong>${sc.vp}</strong></td></tr>
        <tr class='tot'><td>Target VP</td><td><strong>${SOLO_WIN_THRESHOLD}</strong></td></tr>
      </tfoot>
    </table>
    <p style='color:var(--muted);margin-top:8px'>Each maximal ♥/♦ sequence of at least 2 cards is worth ${RED_SEQUENCE_VP} VP.</p>
    <div class='winnerBanner'>🏆 ${G.players[winner].name} wins${targetMet?" by reaching the target":""}</div>
    <div class='optRow'><button id='closeEnd'>Close</button></div>
  `;
  d.querySelector("#closeEnd").onclick=()=>d.close();
  d.showModal();
}

function showSupremacyModal({winner,reason}){
  const d=document.getElementById("modal");
  d.classList.remove("modernSwapModal");
  d.innerHTML=`
    <h3>Game Over</h3>
    <p><strong>${G.players[winner].name}</strong> wins by supremacy.</p>
    <p style='color:var(--muted);margin-top:8px'>Reason: ${reason}</p>
    <div class='winnerBanner'>🏆 ${G.players[winner].name} wins</div>
    <div class='optRow'><button id='closeSup'>Close</button></div>
  `;
  d.querySelector("#closeSup").onclick=()=>d.close();
  d.showModal();
}

function maybeModernSwap(nextFirst){
  return Promise.resolve(nextFirst);
}

function aiSelectMove(){
  const decision=chooseActionWithOptionalJoker();
  if(!decision) return null;
  if(decision.useJoker) useJokerDouble(1);
  return decision.firstIdx;
}

function legalOpenMoves(tableau){
  const acc=accessibility(tableau);
  const moves=[];
  for(let i=0;i<tableau.slots.length;i++){
    const sl=tableau.slots[i];
    if(acc[i] && !isSlotGone(sl) && !sl.faceDown) moves.push(i);
  }
  return moves;
}
function leftmostRightmostOpenMoves(open){
  if(!open.length) return [];
  let left=open[0],right=open[0];
  for(const i of open){
    const sl=G.tableau.slots[i];
    if(sl.gridX<G.tableau.slots[left].gridX) left=i;
    if(sl.gridX>G.tableau.slots[right].gridX) right=i;
  }
  return left===right?[left]:[left,right];
}


function ucbSelect(stats,total,c=0.9){
  let bestIdx=null,best=-Infinity;
  for(const [idx,st] of stats.entries()){
    if(st.n===0) return idx;
    const mean=st.w/st.n;
    const ucb=mean+c*Math.sqrt(Math.log(total)/st.n);
    if(ucb>best){best=ucb;bestIdx=idx;}
  }
  return bestIdx;
}

function cloneGameState(){
  const simTableau={
    slots:G.tableau.slots.map(s=>({
      ...s,
      removed:!!(s.removed||s.pendingAIPick),
      pendingAIPick:false
    })),
    coveredBy:G.tableau.coveredBy,
    coveredByRev:G.tableau.coveredByRev
  };
  hideFaceDownInfoForSim(simTableau);
  return {
    age:G.age,
    current:G.current,
    ended:G.ended,
    nextAgeFirst:G.nextAgeFirst,
    picksLeftThisTurn:G.picksLeftThisTurn,
    players:G.players.map(p=>({cards:p.cards.slice(),joker:p.joker,name:p.name,isAI:p.isAI,feat:cloneFeat(p.feat)})),
    tableau:simTableau,
    decks:{ancient:G.decks.ancient.slice(),modern:G.decks.modern.slice()}
  };
}
function shuffleInPlace(arr){
  for(let i=arr.length-1;i>0;i--){
    const j=(Math.random()*(i+1))|0;
    [arr[i],arr[j]]=[arr[j],arr[i]];
  }
  return arr;
}
function hideFaceDownInfoForSim(tableau){
  const hiddenPool=[];
  for(const slot of tableau.slots){
    if(slot.removed || !slot.faceDown) continue;
    if(slot.card) hiddenPool.push(slot.card);
    slot.card=null;
  }
  tableau.hiddenPool=shuffleInPlace(hiddenPool);
}
function revealHiddenForSim(tableau){
  if(!tableau.hiddenPool || !tableau.hiddenPool.length) return null;
  return tableau.hiddenPool.pop();
}
function accessibilitySim(T){
  const {slots,coveredBy}=T;
  return slots.map((s,i)=>!s.removed && !(coveredBy[i]||[]).some(c=>!slots[c].removed));
}
function checkSupremacySim(S){
  const f0=S.players[0].feat, f1=S.players[1].feat;
  const aiMilitaryDiff=f1.sw-f0.sw;
  if(aiMilitaryDiff>=SOLO_SUPREMACY_THRESHOLD) return 1;

  const aiFoodDiff=f1.cw-f0.cw;
  if(aiFoodDiff>=SOLO_SUPREMACY_THRESHOLD) return 1;

  return null;
}
function flipNewSim(tableau,acc){
  const slots=tableau.slots;
  for(let i=0;i<slots.length;i++){
    if(slots[i].removed || !slots[i].faceDown || !acc[i]) continue;
    slots[i].faceDown=false;
    if(!slots[i].card) slots[i].card=revealHiddenForSim(tableau);
  }
}
function staticTakeValue(S,player,card){
  const f=S.players[player].feat;

  const dSw=(card.suit==="S") ? swordValue(card) : 0;
  const dFood=(card.suit==="C") ? swordValue(card) : 0;

  let dTech=0;
  if(card.suit==="H"){
    const nm=(f.hMask|bitOfRank(card.rank))&MASK13;
    dTech=diamondAdjFromMask(nm)-f.hAdj;
  }

  let dDia=0;
  if(card.suit==="D"){
    const nm=(f.dMask|bitOfRank(card.rank))&MASK13;
    dDia=diamondAdjFromMask(nm)-f.dAdj;
  }

  return dSw*1.25 + dFood*HEURISTIC_WEIGHT_FOOD + dTech*HEURISTIC_WEIGHT_TECH + dDia*HEURISTIC_WEIGHT_DIAMOND;
}
function cheapEvalTake(S,player,idx){
  const slot=S.tableau.slots[idx];
  if(!slot || slot.removed || slot.faceDown) return -Infinity;
  const card=slot.card;
  if(!card) return -Infinity;
  const me=S.players[player].feat;
  const opp=S.players[1-player].feat;

  const dSw=(card.suit==="S") ? swordValue(card) : 0;
  const dFood=(card.suit==="C") ? swordValue(card) : 0;

  let dTech=0;
  if(card.suit==="H"){
    const nm=(me.hMask|bitOfRank(card.rank))&MASK13;
    dTech=diamondAdjFromMask(nm)-me.hAdj;
  }

  let dDia=0;
  if(card.suit==="D"){
    const nm=(me.dMask|bitOfRank(card.rank))&MASK13;
    dDia=diamondAdjFromMask(nm)-me.dAdj;
  }

  const deny=(card.suit==="S" ? 0.24 : 0) + (card.suit==="C" ? 0.24 : 0) + (card.suit==="H" ? 0.14 : 0) + (card.suit==="D" ? 0.14 : 0);
  const pressure=Math.max(0,opp.sw-me.sw-5)*0.05 + Math.max(0,opp.cw-me.cw-5)*0.05;

  const baseScore=dSw*1.25 + dFood*HEURISTIC_WEIGHT_FOOD + dTech*HEURISTIC_WEIGHT_TECH + dDia*HEURISTIC_WEIGHT_DIAMOND + deny + pressure;

  let revealBonus=0;
  const rev=S.tableau.coveredByRev?.[idx] || [];
  for(const upperIdx of rev){
    const upper=S.tableau.slots[upperIdx];
    if(!upper || upper.removed) continue;

    const blockers=S.tableau.coveredBy[upperIdx] || [];
    const becomesAccessible=blockers.every(b=>b===idx || S.tableau.slots[b].removed);
    if(!becomesAccessible) continue;

    const w=upper.faceDown ? 0.35 : 0.18;
    if(upper.card) revealBonus += w * staticTakeValue(S,player,upper.card);
  }

  return baseScore + revealBonus;
}
function choosePlayoutMove(S,eps=0.12){
  const moves=[];
  const acc=accessibilitySim(S.tableau);
  for(let i=0;i<S.tableau.slots.length;i++){
    const sl=S.tableau.slots[i]; if(acc[i]&&!sl.removed&&!sl.faceDown) moves.push(i);
  }
  if(!moves.length) return null;
  if(Math.random()<eps) return moves[Math.floor(Math.random()*moves.length)];
  let best=moves[0], bestV=-Infinity;
  for(const idx of moves){
    const v=cheapEvalTake(S,S.current,idx);
    if(v>bestV){bestV=v;best=idx;}
  }
  return best;
}
function shouldUseJokerInPlayout(S){
  if(!(S.players[S.current].joker && S.picksLeftThisTurn===1)) return false;
  const moves=[];
  const acc=accessibilitySim(S.tableau);
  for(let i=0;i<S.tableau.slots.length;i++){
    const sl=S.tableau.slots[i]; if(acc[i]&&!sl.removed&&!sl.faceDown) moves.push(i);
  }
  if(moves.length<2) return false;
  const player=S.current;
  if(canWinNowWithTwoPicksSim(S,player,moves,2)!==null) return true;
  if(S.age==="ancient" && remainingCardsThisAgeSim(S)>6) return false;
  const vals=moves.map(idx=>cheapEvalTake(S,player,idx)).sort((a,b)=>b-a);
  const single=vals[0];
  const two=vals[0]+0.85*vals[1];
  const reserveBias=S.age==="ancient"?0.35:0.15;
  return two>single+(0.55+reserveBias);
}
function chooseModernSwapSim(S,nextFirst){
  return nextFirst;
}
function bestGreedyMoveForPlayer(S,player){
  const options=legalMovesSim(S);
  if(!options.length) return {idx:null,val:0};
  let bestIdx=options[0],bestVal=-Infinity;
  for(const idx of options){
    const v=cheapEvalTake(S,player,idx);
    if(v>bestVal){bestVal=v; bestIdx=idx;}
  }
  return {idx:bestIdx,val:bestVal};
}
function evaluateModernTurnOneSwing(baseState,nextFirst,aiPlayer=1){
  const second=1-nextFirst;
  const aiAsFirst=cloneState(baseState);
  aiAsFirst.age="modern";
  aiAsFirst.current=second;
  aiAsFirst.picksLeftThisTurn=1;
  aiAsFirst.tableau=buildTableau("modern",makeUnknownModernDeck());
  const firstPick=bestGreedyMoveForPlayer(aiAsFirst,aiPlayer).val;

  const aiAsSecond=cloneState(baseState);
  aiAsSecond.age="modern";
  aiAsSecond.current=nextFirst;
  aiAsSecond.picksLeftThisTurn=1;
  aiAsSecond.tableau=buildTableau("modern",makeUnknownModernDeck());
  const opener=bestGreedyMoveForPlayer(aiAsSecond,nextFirst);
  if(opener.idx!==null) applyTakeSim(aiAsSecond,opener.idx);
  const reply=bestGreedyMoveForPlayer(aiAsSecond,aiPlayer).val;
  return firstPick-reply;
}
function advanceAgeSim(S){
  if(S.age==="ancient"){
    const start=chooseModernSwapSim(S,S.nextAgeFirst,1);
    S.current=start;
    S.picksLeftThisTurn=1;
    S.age="modern";
    S.tableau=buildTableau("modern",makeUnknownModernDeck());
    hideFaceDownInfoForSim(S.tableau);
    return;
  }
  S.ended=true;
}
function playRandomTurn(S){
  const moves=legalMovesSim(S);
  if(!moves.length){S.picksLeftThisTurn=1; S.current=1-S.current; return;}
  if(shouldUseJokerInPlayout(S)){
    S.players[S.current].joker=false;
    S.picksLeftThisTurn=2;
  }
  const idx=choosePlayoutMove(S,0.14);
  if(idx===null){S.picksLeftThisTurn=1;S.current=1-S.current;return;}
  applyTakeSim(S,idx);
}
function legalMovesSim(S){
  const acc=accessibilitySim(S.tableau);
  const res=[];
  for(let i=0;i<S.tableau.slots.length;i++){
    const sl=S.tableau.slots[i]; if(acc[i]&&!sl.removed&&!sl.faceDown) res.push(i);
  }
  return res;
}
function applyTakeSim(S,idx){
  const slot=S.tableau.slots[idx], p=S.players[S.current];
  slot.removed=true; p.cards.push(slot.card);
  updateFeat(p.feat,slot.card);
  S.picksLeftThisTurn=Math.max(0,S.picksLeftThisTurn-1);
  const accAfter=accessibilitySim(S.tableau);
  flipNewSim(S.tableau,accAfter);
  const sup=checkSupremacySim(S); if(sup!==null){S.ended=true; S.winner=sup; return;}
  if(S.tableau.slots.every(s=>s.removed)) advanceAgeSim(S);
  else if(S.picksLeftThisTurn<=0){S.picksLeftThisTurn=1; S.current=1-S.current;}
}
function rewardForState(S,aiPlayer=1){
  if(S.winner!==undefined) return S.winner===aiPlayer?1:0;
  const playerVp=scoreFor(S,0);
  return playerVp>=SOLO_WIN_THRESHOLD ? (aiPlayer===0?1:0) : (aiPlayer===1?1:0);
}
function simulateFromMoveState(baseState,firstIdx,aiPlayer=1){
  const S=cloneState(baseState);
  const slot=S.tableau.slots[firstIdx];
  const acc=accessibilitySim(S.tableau);
  if(!acc[firstIdx]||slot.removed||slot.faceDown) return 0;
  applyTakeSim(S,firstIdx);
  if(S.ended) return rewardForState(S,aiPlayer);
  let guard=500;
  while(!S.ended && guard-->0) playRandomTurn(S);
  return rewardForState(S,aiPlayer);
}
function cloneState(S){
  return {
    age:S.age,current:S.current,ended:S.ended,nextAgeFirst:S.nextAgeFirst,picksLeftThisTurn:S.picksLeftThisTurn,
    players:S.players.map(p=>({cards:p.cards.slice(),joker:p.joker,name:p.name,isAI:p.isAI,feat:cloneFeat(p.feat)})),
    tableau:{
      slots:S.tableau.slots.map(s=>({...s})),
      coveredBy:S.tableau.coveredBy,
      coveredByRev:S.tableau.coveredByRev,
      hiddenPool:(S.tableau.hiddenPool||[]).slice()
    },
    decks:{ancient:S.decks.ancient.slice(),modern:S.decks.modern.slice()},winner:S.winner
  };
}
function estimatePolicyEV(startState,aiPlayer=1,rollouts=64){
  let sum=0;
  for(let i=0;i<rollouts;i++){
    const C=cloneState(startState);
    let guard=600;
    while(!C.ended && guard-->0) playRandomTurn(C);
    sum+=rewardForState(C,aiPlayer);
  }
  return sum/Math.max(1,rollouts);
}
function estimateStateEV(baseState,aiPlayer=1,rollouts=20){
  const options=legalMovesSim(baseState);
  if(!options.length) return rewardForState(baseState,aiPlayer);
  const stats=new Map(options.map(i=>[i,{n:0,w:0}]));
  let total=0;
  for(let i=0;i<rollouts;i++){
    const idx=ucbSelect(stats,++total,0.9);
    const res=simulateFromMoveState(baseState,idx,aiPlayer);
    const st=stats.get(idx); st.n++; st.w+=res;
  }
  let best=0;
  for(const st of stats.values()) best=Math.max(best,st.w/Math.max(1,st.n));
  return best;
}
function selectMoveUcb(baseState,budgetMs=3000,aiPlayer=1){
  const start=performance.now();
  const options=legalMovesSim(baseState);
  if(!options.length) return {idx:null,mean:0};
  const stats=new Map(options.map(i=>[i,{n:0,w:0}]));
  let total=0;
  while(performance.now()-start<budgetMs){
    const idx=ucbSelect(stats,++total,0.9);
    const res=simulateFromMoveState(baseState,idx,aiPlayer);
    const st=stats.get(idx); st.n++; st.w+=res;
  }
  let best=options[0],bestVal=-Infinity;
  for(const [idx,st] of stats.entries()){
    const v=st.w/Math.max(1,st.n);
    if(v>bestVal){bestVal=v;best=idx;}
  }
  return {idx:best,mean:bestVal};
}
function remainingCardsThisAgeSim(S){
  let n=0;
  for(const sl of S.tableau.slots) if(!sl.removed) n++;
  return n;
}
function jokerDecisionThresholdSim(S,player=S.current){
  const left=remainingCardsThisAgeSim(S);
  let threshold=0.08;
  if(S.age==="ancient"){
    if(left>12) threshold=0.11;
    else if(left>7) threshold=0.09;
    else threshold=0.07;
    const t=Math.min(1,Math.max(0,left/18));
    const second=1-S.nextAgeFirst;
    threshold+=0.04+0.05*t;
    if(player===second) threshold+=0.03+0.04*t;
  }else{
    threshold=left>10?0.09:0.06;
  }
  return threshold;
}
function canWinNowWithOnePickSim(S,player=S.current,moves=legalMovesSim(S)){
  for(const idx of moves){
    const C=cloneState(S);
    C.current=player;
    C.picksLeftThisTurn=1;
    applyTakeSim(C,idx);
    if(C.ended && C.winner===player) return idx;
  }
  return null;
}
function canWinNowWithTwoPicksSim(S,player=S.current,moves=legalMovesSim(S),firstCap=4){
  if(!(S.players[player].joker && S.picksLeftThisTurn===1)) return null;
  const firstCand=moves
    .map(i=>({i,v:cheapEvalTake(S,player,i)}))
    .sort((a,b)=>b.v-a.v)
    .slice(0,Math.min(firstCap,moves.length));
  for(const {i:first} of firstCand){
    const C=cloneState(S);
    C.current=player;
    C.players[player].joker=false;
    C.picksLeftThisTurn=2;
    applyTakeSim(C,first);
    if(C.ended && C.winner===player) return first;
    const m2=legalMovesSim(C);
    for(const second of m2){
      const D=cloneState(C);
      applyTakeSim(D,second);
      if(D.ended && D.winner===player) return first;
    }
  }
  return null;
}
function opponentCanWinImmediatelySim(S,opponent){
  const T=cloneState(S);
  T.current=opponent;
  T.picksLeftThisTurn=1;
  if(canWinNowWithOnePickSim(T,opponent)!==null) return true;
  if(T.players[opponent].joker && canWinNowWithTwoPicksSim(T,opponent,legalMovesSim(T),3)!==null) return true;
  return false;
}
function findSafeSingleMoveSim(S,player=S.current){
  const moves=legalMovesSim(S)
    .map(i=>({i,v:cheapEvalTake(S,player,i)}))
    .sort((a,b)=>b.v-a.v)
    .map(x=>x.i);
  for(const idx of moves){
    const C=cloneState(S);
    C.current=player;
    C.picksLeftThisTurn=1;
    applyTakeSim(C,idx);
    if(C.ended && C.winner===player) return idx;
    if(!opponentCanWinImmediatelySim(C,1-player)) return idx;
  }
  return null;
}
function findSafeJokerFirstMoveSim(S,player=S.current){
  if(!(S.players[player].joker && S.picksLeftThisTurn===1)) return null;
  const firstMoves=legalMovesSim(S)
    .map(i=>({i,v:cheapEvalTake(S,player,i)}))
    .sort((a,b)=>b.v-a.v)
    .slice(0,4)
    .map(x=>x.i);
  for(const first of firstMoves){
    const C=cloneState(S);
    C.current=player;
    C.players[player].joker=false;
    C.picksLeftThisTurn=2;
    applyTakeSim(C,first);
    if(C.ended && C.winner===player) return first;
    const secondMoves=legalMovesSim(C)
      .map(i=>({i,v:cheapEvalTake(C,player,i)}))
      .sort((a,b)=>b.v-a.v)
      .slice(0,4)
      .map(x=>x.i);
    for(const second of secondMoves){
      const D=cloneState(C);
      applyTakeSim(D,second);
      if(D.ended && D.winner===player) return first;
      if(!opponentCanWinImmediatelySim(D,1-player)) return first;
    }
  }
  return null;
}
function chooseActionWithOptionalJoker(){
  const base=cloneGameState();
  const forced=legalMovesSim(base);
  if(forced.length===1) return {useJoker:false,firstIdx:forced[0]};
  const canJ=base.players[base.current].joker && base.picksLeftThisTurn===1;

  const winNoJ=canWinNowWithOnePickSim(base,base.current,forced);
  if(winNoJ!==null) return {useJoker:false,firstIdx:winNoJ};

  if(canJ){
    const winWithJ=canWinNowWithTwoPicksSim(base,base.current,forced,4);
    if(winWithJ!==null) return {useJoker:true,firstIdx:winWithJ};

    const safeNoJ=findSafeSingleMoveSim(base,base.current);
    if(safeNoJ===null){
      const safeWithJ=findSafeJokerFirstMoveSim(base,base.current);
      if(safeWithJ!==null) return {useJoker:true,firstIdx:safeWithJ};
    }
  }

  const mainBudgetMs=getAiThinkingBudgetMs(base);
  const noJ=selectMoveUcb(base,mainBudgetMs,1);
  if(!canJ || noJ.idx===null) return {useJoker:false,firstIdx:noJ.idx};
  const yesState=cloneState(base);
  yesState.players[yesState.current].joker=false;
  yesState.picksLeftThisTurn=2;
  const jokerBudgetMs=Math.max(900,Math.round(mainBudgetMs*0.4));
  const yes=selectMoveUcb(yesState,jokerBudgetMs,1);
  const threshold=jokerDecisionThresholdSim(base,base.current);
  if(yes.idx!==null && yes.mean>noJ.mean+threshold) return {useJoker:true,firstIdx:yes.idx};
  return {useJoker:false,firstIdx:noJ.idx};
}
function scoreFor(S,i){
  if(i!==0) return 0;
  return scoreSoloCards(S.players[0].cards).vp;
}

function maybeRunAiTurn(){
  if(aiTimer){clearTimeout(aiTimer); aiTimer=null;}
  return;
}

async function endTurnOrAge(){
  const slots=G.tableau.slots;
  if(slots.every(s=>isSlotGone(s))){
    if(G.age==="ancient"){
      const modernDeck=G.decks.modern.slice();
      const modernTableau=buildTableau("modern",modernDeck);
      const start=await maybeModernSwap(G.nextAgeFirst,modernTableau);
      G.age="modern";
      G.decks.modern=modernDeck;
      G.tableau=modernTableau;
      G.pendingAIRemovals=[];
      G.current=start;
      G.picksLeftThisTurn=1;
      G.phaseTwoOpeningRivalPickPending=true;
      log(`Phase One ends. Phase Two starts with ${G.players[G.current].name}.`);
      if(SOLO_MODE && G.current===1){
        startRivalSelection(null);
        return;
      }
      render(); return;
    }
    G.ended=true;
    const sc=scoreGame();
    const w=sc.vp>=SOLO_WIN_THRESHOLD?0:1;
    log(`Game over. ${G.players[0].name} scored ${sc.vp} VP from ${sc.detail.totalSequences} red sequences. Target: ${SOLO_WIN_THRESHOLD} VP.`);
    log(`🏆 ${G.players[w].name} wins ${w===0?"by reaching the solo target":"because the solo target was not reached"}.`);
    showEndgameModal(sc,w);
    render(); return;
  }
  if(G.awaitingRivalChoice){
    render();
    return;
  }
  if(G.picksLeftThisTurn<=0){
    G.picksLeftThisTurn=1;
    G.current=SOLO_MODE?0:1-G.current;
  }
  render();
}

function render(){
  if(!G) return;
  document.getElementById("agePill").textContent=`Phase: ${G.age==="ancient"?"One":"Two"}`;
  const sideTurn=document.getElementById("sideTurnPill");
  if(G.ended){
    sideTurn.textContent="Turn: -";
    sideTurn.classList.remove("aiTurn");
  }else if(G.awaitingRivalChoice){
    sideTurn.textContent="Turn: AI (choose card)";
    sideTurn.classList.add("aiTurn");
  }else{
    sideTurn.textContent="Turn: You";
    sideTurn.classList.remove("aiTurn");
  }

  const sg=document.getElementById("statusGrid");
  const sw=G.players.map(p=>swords(p.cards));
  const food=G.players.map(p=>foodPower(p.cards));
  const militaryLead=sw[1]-sw[0];
  const foodLead=food[1]-food[0];
  const supremacyLabel=militaryLead===0?"Tie":(militaryLead>0?"AI":"You");
  const foodSupremacyLabel=foodLead===0?"Tie":(foodLead>0?"AI":"You");
  const rivalState=G.awaitingRivalChoice?`Rival pick: ${G.rivalChoiceReason}`:'Rival pick: —';
  sg.innerHTML=`<div class='pill'>♠ Diff: ${supremacyLabel} +${Math.abs(militaryLead)}</div><div class='pill'>♣ Diff: ${foodSupremacyLabel} +${Math.abs(foodLead)}</div><div class='pill'>${rivalState}</div>`;
  const col=document.getElementById("collections");
  col.innerHTML="";
  const culturePlacements=sequencePlacementByPlayer(G.players.map(p=>p.cards),"D");
  const technologyPlacements=sequencePlacementByPlayer(G.players.map(p=>p.cards),"H");
  for(let i=0;i<2;i++){
    const p=G.players[i];
    const el=document.createElement("div"); el.className=`pbox ${G.current===i&&!G.ended?"active":""}`;
    const bySuit={S:[],H:[],D:[],C:[]};
    p.cards.forEach(c=>bySuit[c.suit].push(c));
    const suitMetric={
      S:String(swords(p.cards)),
      H:technologyPlacements[i],
      C:String(foodPower(p.cards)),
      D:culturePlacements[i]
    };
    const suitCols=Object.entries(bySuit).map(([s,cards])=>{
      const sorted=sortCardsByRank(cards);
      const chips=groupedSuitTokens(s,sorted)
        .map(token=>token.cards.length>1
          ? `<span class='runGroup'>${token.cards.map(c=>`<span class='chip s${c.suit}'>${label(c)}</span>`).join("")}</span>`
          : `<span class='chip s${token.cards[0].suit}'>${label(token.cards[0])}</span>`)
        .join("");
      return `<div class='takenCol'><div class='takenTitle'>${SUIT_NAME[s]} (${suitMetric[s]})</div><div class='cardsMini'>${cards.length?chips:"<span class='chip'>—</span>"}</div></div>`;
    }).join("");
    el.innerHTML=`<div class='playerHeader'><strong>${p.name}</strong> (${p.cards.length} cards)</div><div class='takenGrid'>${suitCols}</div>`;
    col.appendChild(el);
  }

  const t=document.getElementById("tableau"); const wrap=t.parentElement;
  const {slots,geom}=G.tableau;
  const wrapStyle=getComputedStyle(wrap);
  const padX=(parseFloat(wrapStyle.paddingLeft)||0)+(parseFloat(wrapStyle.paddingRight)||0);
  const padY=(parseFloat(wrapStyle.paddingTop)||0)+(parseFloat(wrapStyle.paddingBottom)||0);
  const availableW=Math.max(200,wrap.clientWidth-padX);
  const scale=Math.min(1,availableW/geom.width);
  const scaledH=geom.height*scale;
  t.style.width=geom.width+"px";
  t.style.height=geom.height+"px";
  t.style.transform=`scale(${scale})`;
  wrap.style.height=`${Math.ceil(scaledH+padY)}px`;
  t.innerHTML="";
  const acc=accessibility(G.tableau);
  for(let i=0;i<slots.length;i++){
    const s=slots[i];
    const e=document.createElement("div");
    const hasChildren=(G.tableau.coveredBy[i]||[]).some(c=>!isSlotGone(slots[c]));
    const hasParent=(G.tableau.coveredByRev?.[i]||[]).some(p=>!isSlotGone(slots[p]));
    const isRivalChoice=G.awaitingRivalChoice;
    const isRivalValid=isRivalChoice && G.rivalChoiceIndices.includes(i);
    const canOpen=acc[i]&&!s.faceDown&&!isSlotGone(s);
    const isDisabledByRival=isRivalChoice && !isRivalValid;
    e.className=`card ${s.removed?"removed":""} ${s.pendingAIPick?"aiPickedPreview":""} ${s.faceDown?"faceDown":""} ${!s.faceDown&&!isSlotGone(s)?cardClass(s.card):""} ${canOpen&&!isDisabledByRival?"open accessible":""} ${(!canOpen||isDisabledByRival)&&!isSlotGone(s)&&!s.faceDown?"blocked":""} ${hasChildren?"covering":""} ${hasParent?"overlapped":""}`;
    if(isRivalValid) e.classList.add("accessible");
    e.style.left=s.x+"px"; e.style.top=s.y+"px"; e.style.zIndex=String((s.row+1)*100+s.col);
    e.innerHTML=s.faceDown?"<div class='big'>🂠</div>":`<div class='cornerL'></div><div class='cornerR'></div><div class='big'>${label(s.card)}</div>`;
    e.onclick=()=>onHumanCardClick(i);
    t.appendChild(e);
  }
  maybeRunAiTurn();
}

window.addEventListener("resize",scheduleRender);
window.addEventListener("load",()=>{
  scheduleRender();
  requestAnimationFrame(scheduleRender);
});

const tableauWrapEl=document.querySelector(".tableauWrap");
if(tableauWrapEl && typeof ResizeObserver!=="undefined"){
  const tableauResizeObserver=new ResizeObserver(()=>scheduleRender());
  tableauResizeObserver.observe(tableauWrapEl);
}

if(document.fonts?.ready){
  document.fonts.ready.then(()=>scheduleRender());
}

document.getElementById("newGameBtn").onclick=()=>{
  newGame();
};
window.addEventListener("DOMContentLoaded",()=>{
  newGame();
});
