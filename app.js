const SUITS=["S","D","H","C"];
const DIAMOND_VP_AWARDS=[10,6,3];
const MILITARY_VP=5;
const TECHNOLOGY_MAJORITY_VP=5;
const SUIT_NAME={S:"♠ Military",D:"♦ Culture",H:"♥ Technology",C:"♣ Food"};
const SUIT_ICON={S:"♠",D:"♦",H:"♥",C:"♣"};
const SUIT_ABBR={S:"MILI",D:"CULT",H:"TECH",C:"FOOD"};
const RANKS=["A","2","3","4","5","6","7","8","9","10","J","Q","K"];
const RANK_VAL=Object.fromEntries(RANKS.map((r,i)=>[r,i+1]));
const MASK13=(1<<13)-1;
const TABLEAU_MODEL={
  ancient:[
    {faceDown:false,xs:[2,4]},
    {faceDown:true,xs:[1.5,2.5,3.5,4.5]},
    {faceDown:false,xs:[0,1,2,3,4,5,6]},
    {faceDown:true,xs:[0.5,1.5,2.5,3.5,4.5,5.5]},
    {faceDown:false,xs:[1,2,3,4,5]}
  ],
  modern:[
    {faceDown:false,xs:[2,5]},
    {faceDown:true,xs:[1.5,2.5,3.5,4.5,5.5]},
    {faceDown:false,xs:[0,1,2,3,4,5,6,7]},
    {faceDown:true,xs:[0.5,1.5,2.5,3.5,4.5,5.5,6.5]},
    {faceDown:false,xs:[1,2,3,4,5,6]}
  ]
};
let G=null;
let aiTimer=null;
let renderScheduled=false;

const AI_BASE_BUDGET_MS=5000;

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
function ageOf(rank){return ["A","2","3","4","5","6"].includes(rank)?"ancient":"modern";}
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
function techPairGroups(cards){
  const cardByRank=new Map(cards.filter(c=>c.suit==="H").map(c=>[RANK_VAL[c.rank],c]));
  let mask=0;
  for(const rk of cardByRank.keys()) mask|=1<<(rk-1);
  mask&=MASK13;
  const pairs=[];
  for(let start=1;start<=13;start++){
    const a=start;
    const b=(start%13)+1;
    const ranks=[a,b];
    const tMask=(1<<(a-1))|(1<<(b-1));
    if((mask&tMask)===tMask) pairs.push({tMask,ranks});
  }
  if(!pairs.length) return [];
  let bestCount=0;
  let bestMasks=[];
  function dfs(i,used,count,picked){
    if(i>=pairs.length){
      if(count>bestCount){bestCount=count; bestMasks=picked.slice();}
      return;
    }
    dfs(i+1,used,count,picked);
    const t=pairs[i];
    if((used&t.tMask)===0){
      picked.push(t.tMask);
      dfs(i+1,used|t.tMask,count+1,picked);
      picked.pop();
    }
  }
  dfs(0,0,0,[]);
  const pairByMask=new Map(pairs.map(t=>[t.tMask,t.ranks]));
  return bestMasks
    .map(m=>pairByMask.get(m) || [])
    .map(ranks=>ranks.map(r=>cardByRank.get(r)).filter(Boolean))
    .filter(g=>g.length===2)
    .sort((a,b)=>RANK_VAL[a[0].rank]-RANK_VAL[b[0].rank]);
}
function diamondMaximalGroups(cards){
  const cardByRank=new Map(cards.filter(c=>c.suit==="D").map(c=>[RANK_VAL[c.rank],c]));
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
  if(suit==="H"){
    const runs=techPairGroups(sorted);
    const used=new Set(runs.flat().map(c=>c.id));
    const singles=sorted.filter(c=>!used.has(c.id)).map(c=>({key:RANK_VAL[c.rank],cards:[c]}));
    const groups=runs.map(g=>({key:RANK_VAL[g[0].rank],cards:g}));
    return [...singles,...groups].sort((a,b)=>a.key-b.key);
  }
  if(suit==="D"){
    const runs=diamondMaximalGroups(sorted);
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
function techSequenceCountFromMask(mask){
  mask&=MASK13;
  const pairs=[];
  for(let start=1;start<=13;start++){
    const a=start;
    const b=(start%13)+1;
    const tMask=(1<<(a-1))|(1<<(b-1));
    if((mask&tMask)===tMask) pairs.push(tMask);
  }
  if(!pairs.length) return 0;
  let best=0;
  function dfs(i,used,count){
    if(i>=pairs.length){ if(count>best) best=count; return; }
    dfs(i+1,used,count);
    const t=pairs[i];
    if((used&t)===0) dfs(i+1,used|t,count+1);
  }
  dfs(0,0,0);
  return best;
}
function technologyVP(myCount,oppCount){
  return myCount>oppCount?TECHNOLOGY_MAJORITY_VP:0;
}
function diamondAdjFromMask(mask){
  mask&=MASK13;
  const rot=((mask<<1)&MASK13) | (mask>>>12);
  return popcount13(mask&rot);
}
function swordValue(card){
  const v=RANK_VAL[card.rank];
  return (v<=9) ? 1 : 2;
}
function clubValue(card){
  const v=RANK_VAL[card.rank];
  return (v<=9) ? 1 : 2;
}
function kingRiskFromCount(k){
  if(k>=3) return -3;
  if(k===2) return -0.6;
  return 0;
}
function updateFeat(feat,card){
  if(card.suit==="S") feat.sw+=swordValue(card);
  if(card.suit==="H"){
    feat.hMask|=bitOfRank(card.rank);
    feat.hLinks=techSequenceCountFromMask(feat.hMask);
  }
  if(card.suit==="C") feat.cSum+=clubValue(card);
  if(card.suit==="D"){
    feat.dMask|=bitOfRank(card.rank);
    feat.dAdj=diamondAdjFromMask(feat.dMask);
  }
  if(card.rank==="K") feat.kCount+=1;
}
function swords(cards){
  return cards.filter(c=>c.suit==="S").reduce((a,c)=>a+swordValue(c),0);
}
function breakthroughCount(cards){
  const hMask=cards
    .filter(c=>c.suit==="H")
    .reduce((m,c)=>m|bitOfRank(c.rank),0);
  return techSequenceCountFromMask(hMask);
}
function foodVP(cards){
  return cards.filter(c=>c.suit==="C").reduce((a,c)=>a+clubValue(c),0);
}
function hasCalamityMalus(cards){
  return cards.filter(c=>c.rank==="K").length>=3;
}
function diamondSequences(cards){
  const owned=new Set(cards.filter(c=>c.suit==="D").map(c=>RANK_VAL[c.rank]));
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
function culturePlacementByPlayer(playersCards){
  const placements=[[],[]];
  const labels=["1st","2nd","3rd"];
  const ranked=[
    ...diamondSequences(playersCards[0]).map(s=>({...s,owner:0})),
    ...diamondSequences(playersCards[1]).map(s=>({...s,owner:1}))
  ].sort((a,b)=>b.length-a.length || b.high-a.high);
  for(let i=0;i<Math.min(3,ranked.length);i++){
    placements[ranked[i].owner].push(labels[i]);
  }
  return placements.map(p=>p.length?p.join(", "):"—");
}
function scoreGame(){
  const p0=G.players[0].cards,p1=G.players[1].cards;
  const s0=swords(p0),s1=swords(p1);
  const tech0=breakthroughCount(p0), tech1=breakthroughCount(p1);
  const techVP=[technologyVP(tech0,tech1),technologyVP(tech1,tech0)];
  const food0=foodVP(p0), food1=foodVP(p1);
  const calam0=hasCalamityMalus(p0), calam1=hasCalamityMalus(p1);
  const military=[0,0];
  if(s0>s1) military[0]=MILITARY_VP; else if(s1>s0) military[1]=MILITARY_VP;

  const culture=[0,0];
  const seqs=[...diamondSequences(p0).map(s=>({...s,owner:0})),...diamondSequences(p1).map(s=>({...s,owner:1}))]
    .sort((a,b)=>b.length-a.length || b.high-a.high);
  const awards=DIAMOND_VP_AWARDS;
  const cultureAwards=[];
  for(let i=0;i<Math.min(awards.length,seqs.length);i++){
    const award=awards[i];
    culture[seqs[i].owner]+=award;
    cultureAwards.push({owner:seqs[i].owner,vp:award,length:seqs[i].length});
  }

  const vp0=military[0]+food0+techVP[0]+culture[0]-(calam0?5:0);
  const vp1=military[1]+food1+techVP[1]+culture[1]-(calam1?5:0);

  return {
    vp:[vp0,vp1],
    detail:{
      swords:[s0,s1],
      military,
      food:[food0,food1],
      tech:[tech0,tech1],
      techVP,
      culture,
      calamity:[calam0?-5:0,calam1?-5:0],
      cultureAwards
    }
  };
}
function checkSupremacy(){
  const f0=G.players[0].feat, f1=G.players[1].feat;
  if(f0.hLinks>=4) return {winner:0,reason:"Technological Supremacy (>=4 Technological Sequences)"};
  if(f1.hLinks>=4) return {winner:1,reason:"Technological Supremacy (>=4 Technological Sequences)"};
  if(f0.sw - f1.sw >= 7) return {winner:0,reason:"Military Supremacy (>=7 Swords lead)"};
  if(f1.sw - f0.sw >= 7) return {winner:1,reason:"Military Supremacy (>=7 Swords lead)"};
  return null;
}

function newGame(firstPlayer=null){
  const base=shuffle(makeDeck());
  const ancient=shuffle(base.filter(c=>ageOf(c.rank)==="ancient"));
  const modern=shuffle(base.filter(c=>ageOf(c.rank)==="modern"));
  const first=firstPlayer===0||firstPlayer===1?firstPlayer:(Math.random()<0.5?0:1);
  G={
    age:"ancient", nextAgeFirst:1-first, current:first, ended:false,
    decks:{ancient,modern}, tableau:null,
    players:[
      {name:"You",cards:[],joker:true,isAI:false,feat:{sw:0,hMask:0,hLinks:0,cSum:0,dMask:0,dAdj:0,kCount:0}},
      {name:"AI",cards:[],joker:true,isAI:true,feat:{sw:0,hMask:0,hLinks:0,cSum:0,dMask:0,dAdj:0,kCount:0}}
    ],
    lastTaken:null, picksLeftThisTurn:1, modernSwapStillAvailable:false, pendingSwapChoice:null,
    pendingAIRemovals:[]
  };
  G.tableau=buildTableau("ancient",G.decks.ancient);
  log(`New game. ${G.players[G.current].name} starts.`);
  render();
}

function promptChooseStarter({
  title="New Game",
  showConfirmText=true,
  showCancel=true
}={}){
  return new Promise(resolve=>{
    const d=document.getElementById("newGameDialog");
    const confirmLine=showConfirmText?"<p>Are you sure you want to start a new game?</p>":"";
    const cancelRow=showCancel?`<div class='optRow'>
        <button id='newStartCancel'>Cancel</button>
      </div>`:"";
    d.innerHTML=`
      <h3>${title}</h3>
      ${confirmLine}
      <p>Choose who starts:</p>
      <div class='optRow'>
        <button id='newStartHuman' class='primary'>You start</button>
        <button id='newStartAi'>AI starts</button>
      </div>
      ${cancelRow}
    `;
    if(!d.open) d.showModal();
    const close=(choice=null)=>{ if(d.open) d.close(); resolve(choice); };
    d.querySelector("#newStartHuman").onclick=()=>close(0);
    d.querySelector("#newStartAi").onclick=()=>close(1);
    const cancelBtn=d.querySelector("#newStartCancel");
    if(cancelBtn) cancelBtn.onclick=()=>close(null);
    d.oncancel=e=>{
      e.preventDefault();
      if(showCancel) close(null);
    };
  });
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

  if(G.age==="modern" && G.modernSwapStillAvailable) G.modernSwapStillAvailable=false;
  endTurnOrAge();
}

function onHumanCardClick(idx){
  if(!G || G.ended || G.pendingSwapChoice) return;
  if(G.players[G.current].isAI) return;
  takeCard(idx);
}

function canUseJokerDouble(player=G.current){
  return !G.ended && G.current===player && G.players[player].joker && G.picksLeftThisTurn===1 && !G.pendingSwapChoice;
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
  const p0=G.players[0].name, p1=G.players[1].name;
  const rows=[
    {label:"Military",a:sc.detail.military[0],b:sc.detail.military[1]},
    {label:"Food",a:sc.detail.food[0],b:sc.detail.food[1]},
    {label:"Technology",a:sc.detail.techVP[0],b:sc.detail.techVP[1]},
    {label:"Culture",a:sc.detail.culture[0],b:sc.detail.culture[1]},
    {label:"Calamity",a:sc.detail.calamity[0],b:sc.detail.calamity[1]}
  ];
  const cultureText=sc.detail.cultureAwards.length
    ? sc.detail.cultureAwards.map((x,i)=>`${i+1}° ${x.vp} VP → ${G.players[x.owner].name} (sequence ${x.length})`).join("<br>")
    : "No Culture bonus assigned.";
  d.innerHTML=`
    <h3>Game Over</h3>
    <p>Victory points summary:</p>
    <table class='endSummary'>
      <thead>
        <tr><th></th><th>P1</th><th>P2</th></tr>
      </thead>
      <tbody>
        ${rows.map(r=>`<tr><td>${r.label}</td><td><strong>${r.a}</strong></td><td><strong>${r.b}</strong></td></tr>`).join("")}
      </tbody>
      <tfoot>
        <tr class='tot'><td>Total VP</td><td><strong>${sc.vp[0]}</strong></td><td><strong>${sc.vp[1]}</strong></td></tr>
      </tfoot>
    </table>
    <p><strong>${p0}</strong> vs <strong>${p1}</strong></p>
    <p style='color:var(--muted);margin-top:8px'>Bonus Culture: ${cultureText}</p>
    <div class='winnerBanner ${winner===null?"draw":""}'>${winner===null?"🤝 Draw" : `🏆 ${G.players[winner].name} wins`}</div>
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

function maybeModernSwap(nextFirst,modernTableauPreview=null){
  const second=1-nextFirst;
  const pl=G.players[second];
  G.modernSwapStillAvailable=true;
  if(!pl.joker) return Promise.resolve(nextFirst);
  if(pl.isAI){
    const evalStart=performance.now();
    const noSwapState=cloneGameState();
    noSwapState.age="modern";
    noSwapState.current=nextFirst;
    noSwapState.picksLeftThisTurn=1;
    noSwapState.tableau=buildTableau("modern",noSwapState.decks.modern);
    noSwapState.modernSwapStillAvailable=true;
    const swapState=cloneGameState();
    swapState.players[second].joker=false;
    swapState.age="modern";
    swapState.current=second;
    swapState.picksLeftThisTurn=1;
    swapState.tableau=buildTableau("modern",swapState.decks.modern);
    swapState.modernSwapStillAvailable=true;

    // Keep this branch lightweight: it runs during the Ancient->Modern transition
    // on the main thread and can otherwise feel like a UI freeze.
    const transitionRollouts=32;
    const evNo=estimatePolicyEV(noSwapState,1,transitionRollouts);
    const evSwap=estimatePolicyEV(swapState,1,transitionRollouts);
    const turn1Swing=evaluateModernTurnOneSwing(cloneState(noSwapState),nextFirst,1);
    const scoreDelta=(evSwap-evNo) + turn1Swing*0.12;
    const elapsed=performance.now()-evalStart;
    if(elapsed>1200){
      log(`AI evaluates Modern initiative (${elapsed.toFixed(0)}ms).`);
    }
    if(scoreDelta > 0.03){
      pl.joker=false;
      log(`${pl.name} builds Wonder (Seize Initiative) and goes first in the Modern Age.`);
      return Promise.resolve(second);
    }
    return Promise.resolve(nextFirst);
  }
  return new Promise(resolve=>{
    const d=document.getElementById("modal");
    d.classList.add("modernSwapModal");

    G.pendingSwapChoice={type:"modernSwap"};
    if(modernTableauPreview){
      G.tableau=modernTableauPreview;
      render();
    }

    d.innerHTML=`<h3>Modern Age</h3><p>Use Wonder to start first?</p><div class='optRow'><button id='no'>No</button><button id='yes'>Yes</button></div>`;
    d.showModal();
    let settled=false;
    const settle=(value)=>{
      if(settled) return;
      settled=true;
      G.pendingSwapChoice=null;
      d.classList.remove("modernSwapModal");
      resolve(value);
    };
    d.oncancel=()=>{settle(nextFirst);};
    d.querySelector("#no").onclick=()=>{d.close(); settle(nextFirst);};
    d.querySelector("#yes").onclick=()=>{pl.joker=false; d.close(); log(`${pl.name} builds Wonder (Seize Initiative) and goes first in the Modern Age.`); settle(second);};
  });
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
    modernSwapStillAvailable:G.modernSwapStillAvailable,
    players:G.players.map(p=>({cards:p.cards.slice(),joker:p.joker,name:p.name,isAI:p.isAI,feat:{...p.feat}})),
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
  if(f0.hLinks>=4) return 0;
  if(f1.hLinks>=4) return 1;
  if(f0.sw - f1.sw >= 7) return 0;
  if(f1.sw - f0.sw >= 7) return 1;
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

  let dBt=0;
  if(card.suit==="H"){
    const nm=(f.hMask|bitOfRank(card.rank))&MASK13;
    dBt=techSequenceCountFromMask(nm)-f.hLinks;
  }

  let dFood=0;
  if(card.suit==="C"){
    const before=f.cSum;
    const after=f.cSum+clubValue(card);
    dFood=after-before;
  }

  let dDia=0;
  if(card.suit==="D"){
    const nm=(f.dMask|bitOfRank(card.rank))&MASK13;
    dDia=diamondAdjFromMask(nm)-f.dAdj;
  }

  const oldKR=kingRiskFromCount(f.kCount);
  const newKR=kingRiskFromCount(f.kCount + (card.rank==="K" ? 1 : 0));
  const dKing=newKR-oldKR;

  return dSw*1.2 + dBt*1.6 + dFood*1.0 + dDia*0.45 + dKing*1.4;
}
function cheapEvalTake(S,player,idx){
  const slot=S.tableau.slots[idx];
  if(!slot || slot.removed || slot.faceDown) return -Infinity;
  const card=slot.card;
  const me=S.players[player].feat;
  const opp=S.players[1-player].feat;

  const dSw=(card.suit==="S") ? swordValue(card) : 0;

  let dBt=0;
  if(card.suit==="H"){
    const nm=(me.hMask|bitOfRank(card.rank))&MASK13;
    dBt=techSequenceCountFromMask(nm)-me.hLinks;
  }

  let dFood=0;
  if(card.suit==="C"){
    const before=me.cSum;
    const after=me.cSum+clubValue(card);
    dFood=after-before;
  }

  let dDia=0;
  if(card.suit==="D"){
    const nm=(me.dMask|bitOfRank(card.rank))&MASK13;
    dDia=diamondAdjFromMask(nm)-me.dAdj;
  }

  const oldKR=kingRiskFromCount(me.kCount);
  const newKR=kingRiskFromCount(me.kCount + (card.rank==="K" ? 1 : 0));
  const dKing=newKR-oldKR;

  const deny=(card.suit==="S" ? 0.2 : 0) + (card.suit==="H" ? 0.15 : 0);
  const pressure=Math.max(0,opp.sw-me.sw-5)*0.05;

  const baseScore=dSw*1.2 + dBt*1.6 + dFood*1.0 + dDia*0.45 + dKing*1.4 + deny + pressure;

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
function chooseModernSwapSim(S,nextFirst,aiPlayer=1){
  const second=1-nextFirst;
  if(!S.players[second].joker) return nextFirst;
  const noSwap=cloneState(S);
  noSwap.age="modern";
  noSwap.current=nextFirst;
  noSwap.picksLeftThisTurn=1;
  noSwap.tableau=buildTableau("modern",shuffleInPlace(noSwap.decks.modern.slice()));
  hideFaceDownInfoForSim(noSwap.tableau);
  noSwap.modernSwapStillAvailable=true;

  const swap=cloneState(S);
  swap.players[second].joker=false;
  swap.age="modern";
  swap.current=second;
  swap.picksLeftThisTurn=1;
  swap.tableau=buildTableau("modern",shuffleInPlace(swap.decks.modern.slice()));
  hideFaceDownInfoForSim(swap.tableau);
  swap.modernSwapStillAvailable=true;

  const evNo=estimatePolicyEV(noSwap,aiPlayer,16);
  const evSwap=estimatePolicyEV(swap,aiPlayer,16);
  const turn1Swing=evaluateModernTurnOneSwing(S,nextFirst,aiPlayer);
  if((evSwap-evNo) + turn1Swing*0.12 > 0.03){
    S.players[second].joker=false;
    return second;
  }
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
  aiAsFirst.tableau=buildTableau("modern",aiAsFirst.decks.modern.slice());
  const firstPick=bestGreedyMoveForPlayer(aiAsFirst,aiPlayer).val;

  const aiAsSecond=cloneState(baseState);
  aiAsSecond.age="modern";
  aiAsSecond.current=nextFirst;
  aiAsSecond.picksLeftThisTurn=1;
  aiAsSecond.tableau=buildTableau("modern",aiAsSecond.decks.modern.slice());
  const opener=bestGreedyMoveForPlayer(aiAsSecond,nextFirst);
  if(opener.idx!==null) applyTakeSim(aiAsSecond,opener.idx);
  const reply=bestGreedyMoveForPlayer(aiAsSecond,aiPlayer).val;
  return firstPick-reply;
}
function advanceAgeSim(S){
  if(S.age==="ancient"){
    const start=chooseModernSwapSim(S,S.nextAgeFirst,1);
    S.modernSwapStillAvailable=true;
    S.current=start;
    S.picksLeftThisTurn=1;
    S.age="modern";
    S.tableau=buildTableau("modern",shuffleInPlace(S.decks.modern.slice()));
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
  if(S.age==="modern" && S.modernSwapStillAvailable) S.modernSwapStillAvailable=false;
  if(S.tableau.slots.every(s=>s.removed)) advanceAgeSim(S);
  else if(S.picksLeftThisTurn<=0){S.picksLeftThisTurn=1; S.current=1-S.current;}
}
function rewardForState(S,aiPlayer=1){
  if(S.winner!==undefined) return S.winner===aiPlayer?1:0;
  const scAi=scoreFor(S,aiPlayer), scOp=scoreFor(S,1-aiPlayer);
  if(scAi>scOp) return 1;
  if(scAi===scOp) return 0.5;
  return 0;
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
    modernSwapStillAvailable:S.modernSwapStillAvailable,
    players:S.players.map(p=>({cards:p.cards.slice(),joker:p.joker,name:p.name,isAI:p.isAI,feat:{...p.feat}})),
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
  const a=S.players[0].cards,b=S.players[1].cards;
  const sw=[swords(a),swords(b)], tech=[breakthroughCount(a),breakthroughCount(b)];
  let vp=[0,0];
  if(sw[0]>sw[1]) vp[0]+=MILITARY_VP; else if(sw[1]>sw[0]) vp[1]+=MILITARY_VP;
  vp[0]+=foodVP(a); vp[1]+=foodVP(b);
  vp[0]+=technologyVP(tech[0],tech[1]);
  vp[1]+=technologyVP(tech[1],tech[0]);
  if(hasCalamityMalus(a)) vp[0]-=5; if(hasCalamityMalus(b)) vp[1]-=5;
  const seqs=[...diamondSequences(a).map(s=>({...s,o:0})),...diamondSequences(b).map(s=>({...s,o:1}))].sort((x,y)=>y.length-x.length||y.high-x.high);
  DIAMOND_VP_AWARDS.forEach((v,k)=>{if(seqs[k]) vp[seqs[k].o]+=v;});
  return vp[i];
}

function maybeRunAiTurn(){
  if(aiTimer){clearTimeout(aiTimer); aiTimer=null;}
  if(!G||G.ended||G.pendingSwapChoice) return;
  if(!G.players[G.current].isAI) return;
  const forced=legalOpenMoves(G.tableau);
  if(forced.length===0){
    log("AI has no legal pick and passes the turn.");
    G.picksLeftThisTurn=0;
    endTurnOrAge();
    return;
  }
  if(forced.length===1){
    takeCard(forced[0]);
    return;
  }
  aiTimer=setTimeout(()=>{
    if(!G||G.ended||G.current!==1) return;
    const thinkingMs=getAiThinkingBudgetMs(G);
    log(`Monte Carlo AI is thinking (~${(thinkingMs/1000).toFixed(1)}s)...`);
    const idx=aiSelectMove();
    if(idx!==null) takeCard(idx);
  },120);
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
      G.current=start;
      G.picksLeftThisTurn=1;
      log(`Ancient Age ends. Modern Age starts with ${G.players[G.current].name}.`);
      render(); return;
    }
    G.ended=true;
    const sc=scoreGame();
    const w=sc.vp[0]===sc.vp[1]?null:(sc.vp[0]>sc.vp[1]?0:1);
    log(`Game over. VP: ${G.players[0].name} ${sc.vp[0]} - ${G.players[1].name} ${sc.vp[1]}.`);
    log(w===null?"Draw." : `🏆 ${G.players[w].name} wins on points.`);
    showEndgameModal(sc,w);
    render(); return;
  }
  if(G.picksLeftThisTurn<=0){
    G.picksLeftThisTurn=1;
    G.current=1-G.current;
  }
  render();
}

function render(){
  if(!G) return;
  document.getElementById("agePill").textContent=`Age: ${G.age==="ancient"?"Ancient":"Modern"}`;
  const sideTurn=document.getElementById("sideTurnPill");
  if(G.ended){
    sideTurn.textContent="Turn: -";
    sideTurn.classList.remove("aiTurn");
  }else{
    const aiTurn=G.players[G.current].isAI;
    sideTurn.textContent=`Turn: ${aiTurn?"AI":"You"}`;
    sideTurn.classList.toggle("aiTurn",aiTurn);
  }

  const sg=document.getElementById("statusGrid");
  const sw=G.players.map(p=>swords(p.cards)), tp=G.players.map(p=>breakthroughCount(p.cards));
  const militaryLead=sw[1]-sw[0];
  const supremacyLabel=militaryLead===0?"Tie":(militaryLead>0?"AI":"You");
  sg.innerHTML=`<div class='pill'>Tech Seq.: ${tp[0]} / ${tp[1]}</div><div class='pill'>Wonders: ${G.players[0].joker?"✅":"❌"} / ${G.players[1].joker?"✅":"❌"}</div><div class='pill'>Mil. Supr.: ${supremacyLabel} +${Math.abs(militaryLead)}</div>`;

  const useBtn=document.getElementById("useJokerBtn");
  useBtn.disabled=!canUseJokerDouble(0);
  useBtn.onclick=()=>{ if(useJokerDouble(0)) render(); };

  const col=document.getElementById("collections");
  col.innerHTML="";
  const culturePlacements=culturePlacementByPlayer(G.players.map(p=>p.cards));
  for(let i=0;i<2;i++){
    const p=G.players[i];
    const el=document.createElement("div"); el.className=`pbox ${G.current===i&&!G.ended?"active":""}`;
    const bySuit={S:[],H:[],D:[],C:[]};
    p.cards.forEach(c=>bySuit[c.suit].push(c));
    const suitMetric={
      S:String(swords(p.cards)),
      H:String(breakthroughCount(p.cards)),
      C:String(foodVP(p.cards)),
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
    e.className=`card ${s.removed?"removed":""} ${s.pendingAIPick?"aiPickedPreview":""} ${s.faceDown?"faceDown":""} ${!s.faceDown&&!isSlotGone(s)?cardClass(s.card):""} ${acc[i]&&!s.faceDown&&!isSlotGone(s)?"open accessible":""} ${!acc[i]&&!isSlotGone(s)&&!s.faceDown?"blocked":""} ${hasChildren?"covering":""} ${hasParent?"overlapped":""}`;
    e.style.left=s.x+"px"; e.style.top=s.y+"px"; e.style.zIndex=String((s.row+1)*100+s.col);
    e.innerHTML=s.faceDown?"<div class='big'>🂠</div>":`<div class='small'>${SUIT_ABBR[s.card.suit]||SUIT_NAME[s.card.suit]}</div><div class='cornerL'></div><div class='cornerR'></div><div class='big'>${label(s.card)}</div>`;
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

document.getElementById("newGameBtn").onclick=async()=>{
  const first=await promptChooseStarter();
  if(first===null) return;
  newGame(first);
};
document.getElementById("useJokerBtn").onclick=()=>{ if(useJokerDouble(0)) render(); };

window.addEventListener("DOMContentLoaded",async()=>{
  // Prepara subito tutta la UI (tableau/collector/log) dietro al popup iniziale.
  // Usiamo temporaneamente P1 come starter, poi riallineiamo allo starter scelto.
  newGame(0);

  const first=await promptChooseStarter({
    title:"New game",
    showConfirmText:false,
    showCancel:false
  });

  if(first===1) newGame(1);
});
