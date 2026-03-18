(function(){
const SUITS=["S","D","H","C"]; const RANKS=["A","2","3","4","5","6","7","8","9","10","J","Q","K"];
const RED_SEQUENCE_VP=2;
const DEFAULT_SOLO_SUPREMACY_THRESHOLD=4;
const DEFAULT_SOLO_WIN_THRESHOLD=10;
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

const runBtn=document.getElementById("runBtn"), statusEl=document.getElementById("status");
const clamp=(n,min,max)=>Math.max(min,Math.min(max,n));
const mcStrengthInput=document.getElementById("mcStrength");
const supremacyThresholdInput=document.getElementById("supremacyThreshold");
const winThresholdInput=document.getElementById("winThreshold");

function parseIntOrDefault(v,d){const n=Number(v); return Number.isFinite(n)?Math.round(n):d;}
function readMcStrength(){return clamp(parseIntOrDefault(mcStrengthInput.value,1),1,10);}
function normalizeMcStrengthInput(){mcStrengthInput.value=String(readMcStrength());}
function readSupremacyThreshold(){return clamp(parseIntOrDefault(supremacyThresholdInput.value,DEFAULT_SOLO_SUPREMACY_THRESHOLD),1,20);}
function normalizeSupremacyThresholdInput(){supremacyThresholdInput.value=String(readSupremacyThreshold());}
function readWinThreshold(){return clamp(parseIntOrDefault(winThresholdInput.value,DEFAULT_SOLO_WIN_THRESHOLD),1,40);}
function normalizeWinThresholdInput(){winThresholdInput.value=String(readWinThreshold());}
function setParamsFromQuery(){
 const params=new URLSearchParams(location.search);
 if(params.has("mcStrength")) mcStrengthInput.value=params.get("mcStrength");
 if(params.has("supremacyThreshold")) supremacyThresholdInput.value=params.get("supremacyThreshold");
 if(params.has("winThreshold")) winThresholdInput.value=params.get("winThreshold");
 normalizeMcStrengthInput();
 normalizeSupremacyThresholdInput();
 normalizeWinThresholdInput();
}
setParamsFromQuery();
mcStrengthInput.addEventListener("change",normalizeMcStrengthInput);
supremacyThresholdInput.addEventListener("change",normalizeSupremacyThresholdInput);
winThresholdInput.addEventListener("change",normalizeWinThresholdInput);

function mcSettings(level){
 const strength=clamp(parseIntOrDefault(level,1),1,10);
 const tScale=1+0.22*(strength-1);
 const eps=Math.max(0.04,0.2-0.017*(strength-1));
 return {strength,tScale,eps};
}
const DEFAULT_MC_CFG=mcSettings(1);
const HEURISTIC_WEIGHT_FOOD=1.25;
const HEURISTIC_WEIGHT_TECH=0.9;
const HEURISTIC_WEIGHT_DIAMOND=0.9;
const pct=(x,n)=>n?`${(100*x/n).toFixed(1)}%`:"0.0%"; const avg=a=>a.length?a.reduce((x,y)=>x+y,0)/a.length:0;
function median(a){
 if(!a.length) return 0;
 const sorted=a.slice().sort((x,y)=>x-y);
 const mid=Math.floor(sorted.length/2);
 return sorted.length%2===0?(sorted[mid-1]+sorted[mid])/2:sorted[mid];
}
const fmtPct=v=>`${(100*v).toFixed(1)}%`;
function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}
function makeDeck(){const cards=[];let id=0; for(const s of SUITS){for(const r of RANKS){cards.push({id:id++,suit:s,rank:r});}} return cards;}
function getAgeSlotCount(age){return TABLEAU_MODEL[age].reduce((total,row)=>total+row.xs.length,0);}
function splitDeckForAges(deck){
 const shuffled=shuffle(deck.slice());
 const ancientCount=getAgeSlotCount("ancient");
 const modernCount=getAgeSlotCount("modern");
 const ancient=shuffled.slice(0,ancientCount);
 const modern=shuffled.slice(ancientCount,ancientCount+modernCount);
 return {ancient:shuffle(ancient),modern:shuffle(modern)};
}
function buildRows(model){let idx=0; return model.map((cfg,row)=>cfg.xs.map((gridX,col)=>({idx:idx++,row,col,gridX})));}
function buildCovering(rows){const total=rows.reduce((a,r)=>a+r.length,0), coveredBy=Array.from({length:total},()=>[]); for(let r=0;r<rows.length-1;r++){const upper=rows[r],lower=rows[r+1],map=new Map(lower.map(s=>[s.gridX,s.idx])); for(const slot of upper){const c1=map.get(slot.gridX-0.5),c2=map.get(slot.gridX+0.5); if(c1!==undefined) coveredBy[slot.idx].push(c1); if(c2!==undefined) coveredBy[slot.idx].push(c2);}} return coveredBy;}
function buildCoveredByRev(coveredBy){const rev=Array.from({length:coveredBy.length},()=>[]); for(let i=0;i<coveredBy.length;i++) for(const c of coveredBy[i]) rev[c].push(i); return rev;}
function buildTableau(age,deck){const model=TABLEAU_MODEL[age], rows=buildRows(model), covering=buildCovering(rows), slots=[]; for(let row=0;row<model.length;row++){for(let col=0;col<model[row].xs.length;col++){slots.push({card:deck.pop(),removed:false,faceDown:model[row].faceDown,row,col,gridX:model[row].xs[col]});}} return {slots,coveredBy:covering,coveredByRev:buildCoveredByRev(covering)};}
function accessibility(T){const {slots,coveredBy}=T; return slots.map((s,i)=>!s.removed && !(coveredBy[i]||[]).some(c=>!slots[c].removed));}
function flipNew(slots,acc){for(let i=0;i<slots.length;i++) if(!slots[i].removed && slots[i].faceDown && acc[i]) slots[i].faceDown=false;}
function swords(cards){return cards.filter(c=>c.suit==="S").reduce((a,c)=>a+swordValue(c),0);}
function suitSequences(cards,suit){const owned=new Set(cards.filter(c=>c.suit===suit).map(c=>RANK_VAL[c.rank])); if(owned.size<2) return []; const present=i=>owned.has(i===0?13:i===14?1:i); if(owned.size===13) return [{length:13,high:13}]; const seq=[]; for(let i=1;i<=13;i++){if(!owned.has(i) || present(i-1)) continue; let len=1,cur=i; while(present(cur+1)){len++;cur=cur===13?1:cur+1;if(cur===i)break;} if(len>=2){let high=i; for(let k=0,cc=i;k<len;k++){if(cc===13) high=13; else if(high!==13 && cc>high) high=cc; cc=cc===13?1:cc+1;} seq.push({length:len,high});}} return seq;}
function breakthroughCount(cards){return suitSequences(cards,"H").length;}
function diamondSequences(cards){return suitSequences(cards,"D");}
function scoreSoloCards(cards){
 const heartSequences=suitSequences(cards,"H").length;
 const diamondSequencesCount=suitSequences(cards,"D").length;
 const heartVp=heartSequences*RED_SEQUENCE_VP;
 const diamondVp=diamondSequencesCount*RED_SEQUENCE_VP;
 return {
  vp:heartVp+diamondVp,
  heartSequences,
  diamondSequences:diamondSequencesCount,
  heartVp,
  diamondVp,
  totalSequences:heartSequences+diamondSequencesCount
 };
}
function swordValue(card){const v=RANK_VAL[card.rank]; return v<=9?1:2;}
function bitOfRank(rank){ return 1<<(RANK_VAL[rank]-1); }
function popcount13(x){ x>>>=0; let c=0; while(x){ x&=x-1; c++; } return c; }
function diamondAdjFromMask(mask){mask&=MASK13; const rot=((mask<<1)&MASK13) | (mask>>>12); return popcount13(mask&rot);}
function makeFeat(){return {sw:0,cw:0,hMask:0,hAdj:0,dMask:0,dAdj:0};}
function cloneFeat(feat){return {...feat};}
function updateFeat(feat,card){if(card.suit==="S") feat.sw+=swordValue(card); if(card.suit==="C") feat.cw+=swordValue(card); if(card.suit==="H"){feat.hMask|=bitOfRank(card.rank); feat.hAdj=diamondAdjFromMask(feat.hMask);} if(card.suit==="D"){feat.dMask|=bitOfRank(card.rank); feat.dAdj=diamondAdjFromMask(feat.dMask);}}
function checkSupremacy(S,supremacyThreshold){
 const f0=S.players[0].feat, f1=S.players[1].feat;
 if(f1.sw-f0.sw>=supremacyThreshold) return {winner:1,reason:"Military Supremacy"};
 if(f1.cw-f0.cw>=supremacyThreshold) return {winner:1,reason:"Food Supremacy"};
 return null;
}
function legalMoves(S){const acc=accessibility(S.tableau), res=[]; for(let i=0;i<S.tableau.slots.length;i++){const s=S.tableau.slots[i]; if(acc[i] && !s.removed && !s.faceDown) res.push(i);} return res;}

function applyTake(S,player,idx){
 const slot=S.tableau.slots[idx]; if(!slot || slot.removed || slot.faceDown) return false;
 slot.removed=true;
 S.players[player].cards.push(slot.card);
 updateFeat(S.players[player].feat,slot.card);
 flipNew(S.tableau.slots,accessibility(S.tableau));
 const sup=checkSupremacy(S,S.supremacyThreshold);
 if(sup){S.ended=true; S.winBy=sup.reason; S.winner=sup.winner;}
 return true;
}

function leftmostRightmostOpenMoves(S,open){
 if(!open.length) return [];
 let left=open[0], right=open[0];
 for(const idx of open){
  const gx=S.tableau.slots[idx].gridX;
  if(gx<S.tableau.slots[left].gridX) left=idx;
  if(gx>S.tableau.slots[right].gridX) right=idx;
 }
 return left===right?[left]:[left,right];
}
function highValueBlackOpenMoves(S,open){
 return open.filter(i=>{const card=S.tableau.slots[i]?.card; return card && (card.suit==="S"||card.suit==="C") && swordValue(card)===2;});
}
function rivalOptionsForResponse(S){
 const open=legalMoves(S);
 if(open.length<=1) return {options:open,forced:true,reason:"single unlocked card"};
 const black=highValueBlackOpenMoves(S,open);
 if(black.length===1) return {options:black,forced:true,reason:"forced black 2-point"};
 if(black.length>1) return {options:black,forced:false,reason:"black 2-point choice"};
 const lr=leftmostRightmostOpenMoves(S,open);
 return {options:lr,forced:lr.length===1,reason:"leftmost/rightmost"};
}
function rivalOptionsForOpening(S){
 const open=legalMoves(S);
 if(open.length<=1) return {options:open,forced:true,reason:"opening single unlocked card"};
 const black=highValueBlackOpenMoves(S,open);
 if(black.length===1) return {options:black,forced:true,reason:"opening forced black 2-point"};
 if(black.length>1) return {options:black,forced:false,reason:"opening black 2-point choice"};
 const lr=leftmostRightmostOpenMoves(S,open);
 return {options:lr,forced:lr.length===1,reason:"opening leftmost/rightmost"};
}

function stateValueForA(S,rewardMode="insta",winThreshold=DEFAULT_SOLO_WIN_THRESHOLD){
 if(S.winner!==undefined) return S.winner===0?1:0;
 const score=scoreSoloCards(S.players[0].cards);
 if(rewardMode==="scoring"){
  const progress=score.vp/Math.max(1,winThreshold);
  return Math.max(0,Math.min(1,0.15+0.7*progress));
 }
 return score.vp>=winThreshold?1:0;
}
function chooseRivalIdxForA(S,options,rewardMode="insta"){
 if(!options.length) return null;
 if(options.length===1) return options[0];
 return options[Math.floor(Math.random()*options.length)];
}

function cheapEvalTake(S,p,idx){
 const slot=S.tableau.slots[idx]; if(!slot || slot.removed || slot.faceDown) return -1e9; const card=slot.card;
 const me=S.players[p].feat, opp=S.players[1-p].feat;
 let dSw=card.suit==="S"?swordValue(card):0;
 let dFood=card.suit==="C"?swordValue(card):0;
 let dTech=0; if(card.suit==="H"){const nm=(me.hMask|bitOfRank(card.rank))&MASK13; dTech=diamondAdjFromMask(nm)-me.hAdj;}
 let dDia=0; if(card.suit==="D"){const nm=(me.dMask|bitOfRank(card.rank))&MASK13; dDia=diamondAdjFromMask(nm)-me.dAdj;}
 const deny=(card.suit==="S"?0.24:0)+(card.suit==="C"?0.24:0)+(card.suit==="H"?0.14:0)+(card.suit==="D"?0.14:0);
 const danger=Math.max(0,opp.sw+dSw-me.sw-(S.supremacyThreshold-1))*0.35 + Math.max(0,opp.cw+dFood-me.cw-(S.supremacyThreshold-1))*0.35;
 const pressure=Math.max(0,opp.sw-me.sw-(S.supremacyThreshold-2))*0.16 + Math.max(0,opp.cw-me.cw-(S.supremacyThreshold-2))*0.16;
 return dSw*1.1 + dFood*1.1 + dTech*1.4 + dDia*1.4 + deny + pressure + danger;
}

function cloneState(S){return {age:S.age,ended:S.ended,nextAgeFirst:S.nextAgeFirst,supremacyThreshold:S.supremacyThreshold,winThreshold:S.winThreshold,players:S.players.map(p=>({cards:p.cards.slice(),joker:p.joker,feat:cloneFeat(p.feat)})),tableau:{slots:S.tableau.slots.map(s=>({...s})),coveredBy:S.tableau.coveredBy,coveredByRev:S.tableau.coveredByRev},decks:{ancient:S.decks.ancient.slice(),modern:S.decks.modern.slice()},events:{...S.events}};}

function randomPlayout(S,mcCfg=DEFAULT_MC_CFG,rewardMode="insta"){
 let guard=600;
 while(!S.ended && guard-->0){
  if(S.tableau.slots.every(s=>s.removed)){
   if(S.age==="ancient"){
    S.age="modern";
    S.tableau=buildTableau("modern",S.decks.modern);
    const openR=rivalOptionsForOpening(S);
    if(openR.options.length){
      const ridx=chooseRivalIdxForA(S,openR.options,rewardMode);
      if(ridx!==null) applyTake(S,1,ridx);
      S.events.rivalChoices+=openR.options.length>1?1:0;
      S.events.rivalForced+=openR.options.length<=1?1:0;
    }
    continue;
   }
   break;
  }
  const moves=legalMoves(S);
  if(!moves.length) break;
  let idx;
  if(Math.random()<mcCfg.eps) idx=moves[Math.floor(Math.random()*moves.length)];
  else {
   idx=moves[0]; let best=-Infinity;
   for(const m of moves){const v=cheapEvalTake(S,0,m); if(v>best){best=v; idx=m;}}
  }
  const card=S.tableau.slots[idx].card;
  applyTake(S,0,idx);
  if(S.ended) continue;
  if(S.tableau.slots.every(s=>s.removed)) continue;
  const rr=rivalOptionsForResponse(S);
  if(rr.options.length){
   const ridx=chooseRivalIdxForA(S,rr.options,rewardMode);
   if(ridx!==null) applyTake(S,1,ridx);
   S.events.rivalChoices+=rr.options.length>1?1:0;
   S.events.rivalForced+=rr.options.length<=1?1:0;
  }
 }
 return stateValueForA(S,rewardMode,S.winThreshold);
}
function ucbSelect(stats,total,c=0.9){let bestIdx=null,best=-Infinity; for(const [idx,st] of stats.entries()){if(st.n===0) return idx; const mean=st.w/st.n; const ucb=mean+c*Math.sqrt(Math.log(total)/st.n); if(ucb>best){best=ucb;bestIdx=idx;}} return bestIdx;}
function chooseMoveUcb(S,moves,mcCfg,{topK=4,rewardMode="insta",exploration=0.85,tBias=1}={}){
 const ordered=moves.map(i=>({idx:i,v:cheapEvalTake(S,0,i)})).sort((a,b)=>b.v-a.v);
 const cand=ordered.slice(0,Math.min(topK,ordered.length)).map(x=>x.idx);
 const left=S.tableau.slots.reduce((n,s)=>n+(!s.removed?1:0),0);
 let T=S.age==="ancient"?10:14; if(left<=12) T=20; if(left<=8) T=28;
 T=Math.max(1,Math.round(T*mcCfg.tScale*tBias));
 const stats=new Map(cand.map(i=>[i,{n:0,w:0}]));
 let total=0;
 for(let t=0;t<T;t++){
  const idx=ucbSelect(stats,++total,exploration);
  const C=cloneState(S);
  const card=C.tableau.slots[idx].card;
  applyTake(C,0,idx);
  if(!C.ended){
   const rr=rivalOptionsForResponse(C);
   if(rr.options.length){
    const ridx=chooseRivalIdxForA(C,rr.options,rewardMode);
    if(ridx!==null) applyTake(C,1,ridx);
   }
  }
  const r=randomPlayout(C,mcCfg,rewardMode);
  const st=stats.get(idx); st.n++; st.w+=r;
 }
 let best=cand[0],bestV=-Infinity;
 for(const [idx,st] of stats.entries()){const v=st.w/Math.max(1,st.n); if(v>bestV){bestV=v;best=idx;}}
 return best;
}

function chooseMoveA(S,strategy,mcCfg){
 const moves=legalMoves(S);
 if(!moves.length) return null;
 if(moves.length===1) return moves[0];
 if(strategy==="random") return moves[Math.floor(Math.random()*moves.length)];
 if(strategy==="greedy"){let best=moves[0],bestV=-Infinity; for(const idx of moves){const v=cheapEvalTake(S,0,idx); if(v>bestV){bestV=v; best=idx;}} return best;}
 if(strategy==="mc"||strategy==="mc_insta_win") return chooseMoveUcb(S,moves,mcCfg,{topK:4,rewardMode:"insta",exploration:0.85,tBias:1});
 return chooseMoveUcb(S,moves,mcCfg,{topK:5,rewardMode:"scoring",exploration:0.75,tBias:1.25});
}

function shouldUseJokerForPlayer(S,moves){
 if(!S.players[0].joker || moves.length<2) return false;
 const sorted=moves
  .map(i=>cheapEvalTake(S,0,i))
  .sort((a,b)=>b-a);
 const bestSingle=sorted[0]||-Infinity;
 const bestDouble=(sorted[0]||-Infinity)+0.85*(sorted[1]||-Infinity);
 const remaining=S.tableau.slots.reduce((n,s)=>n+(!s.removed?1:0),0);
 const reserveBias=S.age==="ancient" && remaining>10 ? 0.35 : 0.15;
 return bestDouble>bestSingle+(0.55+reserveBias);
}

function maybeAdvanceAge(S){
 if(!S.tableau.slots.every(s=>s.removed) || S.ended) return;
 if(S.age==="ancient"){
  const modernFirst=S.nextAgeFirst;
  S.age="modern";
  S.tableau=buildTableau("modern",S.decks.modern);
  if(modernFirst===1){
   const rr=rivalOptionsForOpening(S);
   if(rr.options.length){
    const ridx=chooseRivalIdxForA(S,rr.options,"insta");
    if(ridx!==null) applyTake(S,1,ridx);
    S.events.rivalChoices+=rr.options.length>1?1:0;
    S.events.rivalForced+=rr.options.length<=1?1:0;
   }
  }
  return;
 }
 S.ended=true;
}

function simulateOne(startPlayer,strA,mcCfg,supremacyThreshold,winThreshold){
 const {ancient,modern}=splitDeckForAges(makeDeck());
 const firstPlayer=startPlayer===1?1:0;
 const S={age:"ancient",nextAgeFirst:1-firstPlayer,ended:false,supremacyThreshold,winThreshold,decks:{ancient,modern},tableau:buildTableau("ancient",ancient),players:[{cards:[],joker:false,feat:makeFeat()},{cards:[],joker:false,feat:makeFeat()}],events:{rivalForced:0,rivalChoices:0}};

 if(firstPlayer===1){
  const openingRival=rivalOptionsForOpening(S);
  if(openingRival.options.length){
   const ridx=chooseRivalIdxForA(S,openingRival.options,"insta");
   if(ridx!==null) applyTake(S,1,ridx);
   S.events.rivalChoices+=openingRival.options.length>1?1:0;
   S.events.rivalForced+=openingRival.options.length<=1?1:0;
  }
 }

 let guard=1200;
 while(!S.ended && guard-->0){
  maybeAdvanceAge(S);
  if(S.ended) break;
  const openingMoves=legalMoves(S);
  if(!openingMoves.length){S.ended=true; break;}

  const picksThisTurn=shouldUseJokerForPlayer(S,openingMoves)?2:1;
  if(picksThisTurn===2) S.players[0].joker=false;

  let lastPlayerCard=null;
  for(let pick=0;pick<picksThisTurn;pick++){
   const mv=chooseMoveA(S,strA,mcCfg);
   if(mv===null){S.ended=true; break;}
   lastPlayerCard=S.tableau.slots[mv].card;
   applyTake(S,0,mv);
   if(S.ended) break;
   if(S.tableau.slots.every(s=>s.removed)) break;
  }
  if(S.ended){maybeAdvanceAge(S); continue;}
  if(S.tableau.slots.every(s=>s.removed)){maybeAdvanceAge(S); continue;}

  if(lastPlayerCard){
   const rr=rivalOptionsForResponse(S);
   if(rr.options.length){
    const ridx=chooseRivalIdxForA(S,rr.options,"insta");
    if(ridx!==null) applyTake(S,1,ridx);
    S.events.rivalChoices+=rr.options.length>1?1:0;
    S.events.rivalForced+=rr.options.length<=1?1:0;
   }
  }
  maybeAdvanceAge(S);
 }
 const score=scoreSoloCards(S.players[0].cards);
 const vpA=score.vp;
 const winner=S.winner!==undefined?(S.winner===0?"a":"b"):(vpA>=S.winThreshold?"a":"b");
 const winBy=S.winBy || (vpA>=S.winThreshold?"Target VP":"Below target VP");
 return {vpA,winner,winBy,score,events:S.events,winThreshold:S.winThreshold};
}
function renderRows(tbody,rows){tbody.innerHTML=rows.map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td>${r[2]!==undefined?`<td>${r[2]}</td>`:""}</tr>`).join("");}
function renderHistogram(values){const upper=Math.max(12,...values,readWinThreshold()+2),step=2,buckets=new Map(); for(let x=0;x<=upper;x+=step) buckets.set(`${x}..${x+step-1}`,0); const overflowKey=`>=${upper+1}`; buckets.set(overflowKey,0); for(const v of values){if(v>upper)buckets.set(overflowKey,buckets.get(overflowKey)+1); else {const start=Math.floor(Math.max(0,v)/step)*step,key=`${start}..${start+step-1}`; buckets.set(key,(buckets.get(key)||0)+1);}} const total=Math.max(1,values.length),maxN=Math.max(1,...buckets.values()); document.getElementById("marginHist").innerHTML=[...buckets.entries()].map(([k,v])=>`<div class="bar"><div>${k}</div><div class="track"><div class="fill" style="width:${Math.round(100*v/maxN)}%"></div></div><div>${(100*v/total).toFixed(1)}%</div></div>`).join("");}
async function runBatch(){const n=Math.max(1,Math.min(10000,Number(document.getElementById("games").value)||1000)); const sA=document.getElementById("playerStrategy").value, sm=document.getElementById("startMode").value, mcCfg=mcSettings(readMcStrength()), supremacyThreshold=readSupremacyThreshold(), winThreshold=readWinThreshold();
 normalizeSupremacyThresholdInput();
 normalizeWinThresholdInput();
 runBtn.disabled=true; const out=[]; let lastUiTick=performance.now();
 for(let i=0;i<n;i++){
  const start=sm==="alternate"?(i%2):sm==="a"?0:1;
  out.push(simulateOne(start,sA,mcCfg,supremacyThreshold,winThreshold));
  const done=i+1;
  const now=performance.now();
  if(done===n || now-lastUiTick>=33){
   statusEl.textContent=`Simulation running: ${done}/${n}`;
   lastUiTick=now;
   await new Promise(r=>setTimeout(r,0));
  }
 }
 const aWin=out.filter(x=>x.winner==="a").length,bWin=out.filter(x=>x.winner==="b").length,draw=out.length-aWin-bWin;
 const targetWins=out.filter(x=>x.winBy==="Target VP").length;
 const underTargetLosses=out.filter(x=>x.winBy==="Below target VP").length;
 const supremacyLosses=out.filter(x=>x.winBy.includes("Supremacy")).length;
 const vpValues=out.map(x=>x.vpA);
 document.getElementById("kGames").textContent=String(out.length); document.getElementById("kAWin").textContent=pct(aWin,out.length); document.getElementById("kBWin").textContent=pct(bWin,out.length); document.getElementById("kDraw").textContent=pct(draw,out.length);
 renderHistogram(vpValues);
 renderRows(document.getElementById("scoreTable"),[["Target VP",String(winThreshold)],["Average VP (all games)",avg(vpValues).toFixed(2)],["Median VP",median(vpValues)],["Average total red sequences",avg(out.map(x=>x.score.totalSequences)).toFixed(2)],["Average VP in target wins",avg(out.filter(x=>x.winner==="a").map(x=>x.vpA)).toFixed(2)]]);
 renderRows(document.getElementById("eventTable"),[["Military Supremacy",pct(out.filter(x=>x.winBy==="Military Supremacy").length,out.length)],["Food Supremacy",pct(out.filter(x=>x.winBy==="Food Supremacy").length,out.length)],["Wins by reaching target",pct(targetWins,out.length)],["Losses below target",pct(underTargetLosses,out.length)],["All supremacy losses",pct(supremacyLosses,out.length)],["Rival forced picks",avg(out.map(x=>x.events.rivalForced)).toFixed(2)+" / game"],["Rival non-forced picks",avg(out.map(x=>x.events.rivalChoices)).toFixed(2)+" / game"]]);
 renderRows(document.getElementById("vpTable"),[["♥ sequences",avg(out.map(x=>x.score.heartSequences)).toFixed(2)],["♦ sequences",avg(out.map(x=>x.score.diamondSequences)).toFixed(2)],["♥ VP",avg(out.map(x=>x.score.heartVp)).toFixed(2)],["♦ VP",avg(out.map(x=>x.score.diamondVp)).toFixed(2)],["Total red-sequence VP",avg(vpValues).toFixed(2)]]);
 statusEl.textContent=`Completed: ${n} games.`; runBtn.disabled=false;}
runBtn.addEventListener("click",runBatch);
statusEl.textContent="Ready. Solo-mode statistical core loaded.";
})();
