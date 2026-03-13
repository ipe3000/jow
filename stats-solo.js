(function(){
const SUITS=["S","D","H","C"]; const RANKS=["A","2","3","4","5","6","7","8","9","10","J","Q","K"];
const DIAMOND_VP_AWARDS=[6,3,1];
const TOP_THREE_SWEEP_BONUS=3;
const MILITARY_VP=2;
const SOLO_SUPREMACY_THRESHOLD_AI=5;
const SOLO_SUPREMACY_THRESHOLD_HUMAN=10;
const CALAMITY_VP_PENALTY=-2;
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

function parseIntOrDefault(v,d){const n=Number(v); return Number.isFinite(n)?Math.round(n):d;}
function readMcStrength(){return clamp(parseIntOrDefault(mcStrengthInput.value,1),1,10);}
function normalizeMcStrengthInput(){mcStrengthInput.value=String(readMcStrength());}
function setParamsFromQuery(){
 const params=new URLSearchParams(location.search);
 if(params.has("mcStrength")) mcStrengthInput.value=params.get("mcStrength");
 normalizeMcStrengthInput();
}
setParamsFromQuery();
mcStrengthInput.addEventListener("change",normalizeMcStrengthInput);

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
function compareSequences(a,b,{ignoreHigh=false,rivalWinsTie=false}={}){if(!a&&!b)return rivalWinsTie?-1:0; if(!a)return -1; if(!b)return 1; if(a.length!==b.length)return a.length>b.length?1:-1; if(!ignoreHigh&&a.high!==b.high)return a.high>b.high?1:-1; return rivalWinsTie?-1:0;}
function bestRedSuitSequence(cards){
 const best=suit=>{const seq=suitSequences(cards,suit); if(!seq.length) return null; return seq.slice().sort((x,y)=>y.length-x.length)[0];};
 const h=best("H"), d=best("D"), cmp=compareSequences(h,d,{ignoreHigh:true});
 return cmp>=0?h:d;
}
function winnerOnVpWithRedTieBreak(cardsA,cardsB,vpA,vpB){
 if(vpA!==vpB) return vpA>vpB?0:1;
 const redA=bestRedSuitSequence(cardsA), redB=bestRedSuitSequence(cardsB);
 const cmp=compareSequences(redA,redB,{ignoreHigh:true,rivalWinsTie:true});
 return cmp>0?0:1;
}
function foodPower(cards){return cards.filter(c=>c.suit==="C").reduce((a,c)=>a+swordValue(c),0);}
function calamityPenalty(cards,applyPenalty=true){
 if(!applyPenalty) return 0;
 const kings=cards.filter(c=>c.rank==="K").length;
 return kings>=1?CALAMITY_VP_PENALTY:0;
}
function awardTopThreePlacements(seqs){
 const vp=[0,0], placements=[];
 for(let i=0;i<Math.min(DIAMOND_VP_AWARDS.length,seqs.length);i++){
  const award=DIAMOND_VP_AWARDS[i], owner=seqs[i].o;
  vp[owner]+=award;
  placements.push({owner,vp:award,length:seqs[i].length});
 }
 let sweepBonusOwner=null;
 if(placements.length===3 && placements.every(p=>p.owner===placements[0].owner)){
  sweepBonusOwner=placements[0].owner;
  vp[sweepBonusOwner]+=TOP_THREE_SWEEP_BONUS;
 }
 return {vp,placements,sweepBonusOwner};
}
function scoreFromCards(a,b){
 const sw=[swords(a),swords(b)], foodPowerByPlayer=[foodPower(a),foodPower(b)]; let vp=[0,0], military=[0,0], food=[0,0];
 if(sw[0]>sw[1]) military=[MILITARY_VP,0]; else if(sw[1]>sw[0]) military=[0,MILITARY_VP];
 if(foodPowerByPlayer[0]>foodPowerByPlayer[1]) food=[MILITARY_VP,0]; else if(foodPowerByPlayer[1]>foodPowerByPlayer[0]) food=[0,MILITARY_VP];
 vp[0]+=military[0]+food[0]; vp[1]+=military[1]+food[1];
 const techSeqs=[...suitSequences(a,"H").map(s=>({...s,o:0})),...suitSequences(b,"H").map(s=>({...s,o:1}))].sort((x,y)=>(y.length-x.length)||(y.o-x.o));
 const techTopThree=awardTopThreePlacements(techSeqs);
 const tech=[...techTopThree.vp]; vp[0]+=tech[0]; vp[1]+=tech[1];
 const seqs=[...diamondSequences(a).map(s=>({...s,o:0})),...diamondSequences(b).map(s=>({...s,o:1}))].sort((x,y)=>(y.length-x.length)||(y.o-x.o));
 const cultureTopThree=awardTopThreePlacements(seqs);
 const culture=[...cultureTopThree.vp]; vp[0]+=culture[0]; vp[1]+=culture[1];
 const calamity=[calamityPenalty(a,true),calamityPenalty(b,false)]; vp[0]+=calamity[0]; vp[1]+=calamity[1];
 return {vp,military,food,tech,culture,calamity,swords:sw,breakthrough:[breakthroughCount(a),breakthroughCount(b)]};
}
function swordValue(card){const v=RANK_VAL[card.rank]; return v<=9?1:2;}
function bitOfRank(rank){ return 1<<(RANK_VAL[rank]-1); }
function popcount13(x){ x>>>=0; let c=0; while(x){ x&=x-1; c++; } return c; }
function diamondAdjFromMask(mask){mask&=MASK13; const rot=((mask<<1)&MASK13) | (mask>>>12); return popcount13(mask&rot);}
function makeFeat(){return {sw:0,cw:0,hMask:0,hAdj:0,dMask:0,dAdj:0};}
function cloneFeat(feat){return {...feat};}
function updateFeat(feat,card){if(card.suit==="S") feat.sw+=swordValue(card); if(card.suit==="C") feat.cw+=swordValue(card); if(card.suit==="H"){feat.hMask|=bitOfRank(card.rank); feat.hAdj=diamondAdjFromMask(feat.hMask);} if(card.suit==="D"){feat.dMask|=bitOfRank(card.rank); feat.dAdj=diamondAdjFromMask(feat.dMask);}}
function checkSupremacy(S){const f0=S.players[0].feat, f1=S.players[1].feat; if(f0.sw-f1.sw>=SOLO_SUPREMACY_THRESHOLD_HUMAN) return {winner:0,reason:"Military Supremacy"}; if(f1.sw-f0.sw>=SOLO_SUPREMACY_THRESHOLD_AI) return {winner:1,reason:"Military Supremacy"}; if(f0.cw-f1.cw>=SOLO_SUPREMACY_THRESHOLD_HUMAN) return {winner:0,reason:"Food Supremacy"}; if(f1.cw-f0.cw>=SOLO_SUPREMACY_THRESHOLD_AI) return {winner:1,reason:"Food Supremacy"}; return null;}
function legalMoves(S){const acc=accessibility(S.tableau), res=[]; for(let i=0;i<S.tableau.slots.length;i++){const s=S.tableau.slots[i]; if(acc[i] && !s.removed && !s.faceDown) res.push(i);} return res;}

function applyTake(S,player,idx){
 const slot=S.tableau.slots[idx]; if(!slot || slot.removed || slot.faceDown) return false;
 slot.removed=true;
 S.players[player].cards.push(slot.card);
 updateFeat(S.players[player].feat,slot.card);
 flipNew(S.tableau.slots,accessibility(S.tableau));
 const sup=checkSupremacy(S);
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
function rivalOptionsForResponse(S,playerCard){
 const open=legalMoves(S);
 if(open.length<=1) return {options:open,forced:true,reason:"single unlocked card"};
 const black=highValueBlackOpenMoves(S,open);
 if(black.length===1) return {options:black,forced:true,reason:"forced black 2-point"};
 if(black.length>1) return {options:black,forced:false,reason:"black 2-point choice"};
 const sameSuit=open.filter(i=>S.tableau.slots[i].card.suit===playerCard.suit);
 if(sameSuit.length===1) return {options:sameSuit,forced:true,reason:"forced same suit"};
 if(sameSuit.length>1) return {options:sameSuit,forced:false,reason:"same suit choice"};
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

function stateValueForA(S,rewardMode="insta"){
 if(S.winner!==undefined) return S.winner===0?1:0;
 const sc=scoreFromCards(S.players[0].cards,S.players[1].cards).vp;
 if(rewardMode==="scoring"){
  const margin=sc[0]-sc[1];
  return 0.5+0.5*Math.max(-1,Math.min(1,margin/20));
 }
 const w=winnerOnVpWithRedTieBreak(S.players[0].cards,S.players[1].cards,sc[0],sc[1]);
 return w===0?1:0;
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
 const pressure=Math.max(0,opp.sw-me.sw-5)*0.05 + Math.max(0,opp.cw-me.cw-5)*0.05;
 return dSw*1.25 + dFood*HEURISTIC_WEIGHT_FOOD + dTech*HEURISTIC_WEIGHT_TECH + dDia*HEURISTIC_WEIGHT_DIAMOND + deny + pressure;
}

function cloneState(S){return {age:S.age,ended:S.ended,nextAgeFirst:S.nextAgeFirst,players:S.players.map(p=>({cards:p.cards.slice(),joker:p.joker,feat:cloneFeat(p.feat)})),tableau:{slots:S.tableau.slots.map(s=>({...s})),coveredBy:S.tableau.coveredBy,coveredByRev:S.tableau.coveredByRev},decks:{ancient:S.decks.ancient.slice(),modern:S.decks.modern.slice()},events:{...S.events}};}

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
  const rr=rivalOptionsForResponse(S,card);
  if(rr.options.length){
   const ridx=chooseRivalIdxForA(S,rr.options,rewardMode);
   if(ridx!==null) applyTake(S,1,ridx);
   S.events.rivalChoices+=rr.options.length>1?1:0;
   S.events.rivalForced+=rr.options.length<=1?1:0;
  }
 }
 return stateValueForA(S,rewardMode);
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
   const rr=rivalOptionsForResponse(C,card);
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

function simulateOne(startPlayer,strA,mcCfg){
 const {ancient,modern}=splitDeckForAges(makeDeck());
 const firstPlayer=startPlayer===1?1:0;
 const S={age:"ancient",nextAgeFirst:1-firstPlayer,ended:false,decks:{ancient,modern},tableau:buildTableau("ancient",ancient),players:[{cards:[],joker:true,feat:makeFeat()},{cards:[],joker:false,feat:makeFeat()}],events:{rivalForced:0,rivalChoices:0}};

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
   const rr=rivalOptionsForResponse(S,lastPlayerCard);
   if(rr.options.length){
    const ridx=chooseRivalIdxForA(S,rr.options,"insta");
    if(ridx!==null) applyTake(S,1,ridx);
    S.events.rivalChoices+=rr.options.length>1?1:0;
    S.events.rivalForced+=rr.options.length<=1?1:0;
   }
  }
  maybeAdvanceAge(S);
 }
 const score=scoreFromCards(S.players[0].cards,S.players[1].cards);
 const vpA=score.vp[0], vpB=score.vp[1];
 const pointsWinner=winnerOnVpWithRedTieBreak(S.players[0].cards,S.players[1].cards,vpA,vpB);
 const winner=S.winner!==undefined?(S.winner===0?"a":"b"):(pointsWinner===0?"a":"b");
 const winBy=S.winBy || "Points";
 return {vpA,vpB,margin:vpB-vpA,winner,winBy,score,events:S.events};
}
function renderRows(tbody,rows){tbody.innerHTML=rows.map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td>${r[2]!==undefined?`<td>${r[2]}</td>`:""}</tr>`).join("");}
function renderHistogram(margins){const buckets=new Map(); for(let x=-20;x<=20;x+=4) buckets.set(`${x}..${x+3}`,0); buckets.set("<=-21",0); buckets.set(">=21",0); for(const m of margins){if(m<=-21)buckets.set("<=-21",buckets.get("<=-21")+1); else if(m>=21)buckets.set(">=21",buckets.get(">=21")+1); else {const b=Math.floor((m+20)/4),s=-20+b*4,key=`${s}..${s+3}`; buckets.set(key,buckets.get(key)+1);}} const total=Math.max(1,margins.length),maxN=Math.max(1,...buckets.values()); document.getElementById("marginHist").innerHTML=[...buckets.entries()].map(([k,v])=>`<div class="bar"><div>${k}</div><div class="track"><div class="fill" style="width:${Math.round(100*v/maxN)}%"></div></div><div>${(100*v/total).toFixed(1)}%</div></div>`).join("");}
async function runBatch(){const n=Math.max(1,Math.min(10000,Number(document.getElementById("games").value)||1000)); const sA=document.getElementById("playerStrategy").value, sm=document.getElementById("startMode").value, mcCfg=mcSettings(readMcStrength());
 runBtn.disabled=true; const out=[]; let lastUiTick=performance.now();
 for(let i=0;i<n;i++){
  const start=sm==="alternate"?(i%2):sm==="a"?0:1;
  out.push(simulateOne(start,sA,mcCfg));
  const done=i+1;
  const now=performance.now();
  if(done===n || now-lastUiTick>=33){
   statusEl.textContent=`Simulation running: ${done}/${n}`;
   lastUiTick=now;
   await new Promise(r=>setTimeout(r,0));
  }
 }
 const aWin=out.filter(x=>x.winner==="a").length,bWin=out.filter(x=>x.winner==="b").length,draw=out.length-aWin-bWin;
 const nonDraw=Math.max(1,aWin+bWin), pB=bWin/nonDraw, pA=aWin/nonDraw;
 const se=Math.sqrt(0.25/nonDraw), ci95=1.96*se, delta=pB-pA;
 const significance=Math.abs(delta)<=ci95?"Difference compatible with statistical variance":"Difference beyond the 95% band (verify with more games)";
 const pointsOnly=out.filter(x=>x.winBy==="Points");
 document.getElementById("kGames").textContent=String(out.length); document.getElementById("kAWin").textContent=pct(aWin,out.length); document.getElementById("kBWin").textContent=pct(bWin,out.length); document.getElementById("kDraw").textContent=pct(draw,out.length);
 const margins=out.map(x=>x.margin); renderHistogram(margins);
 renderRows(document.getElementById("scoreTable"),[["Average VP",avg(out.map(x=>x.vpA)).toFixed(2),avg(out.map(x=>x.vpB)).toFixed(2)],["Median VP",out.map(x=>x.vpA).sort((a,b)=>a-b)[Math.floor(out.length/2)],out.map(x=>x.vpB).sort((a,b)=>a-b)[Math.floor(out.length/2)]],["Average margin (B-A)",avg(margins).toFixed(2),"—"],["Supremacy wins",pct(out.filter(x=>x.winBy.includes("Supremacy") && x.winner==="a").length,out.length),pct(out.filter(x=>x.winBy.includes("Supremacy") && x.winner==="b").length,out.length)]]);
 renderRows(document.getElementById("eventTable"),[["Military Supremacy",pct(out.filter(x=>x.winBy==="Military Supremacy").length,out.length)],["Food Supremacy",pct(out.filter(x=>x.winBy==="Food Supremacy").length,out.length)],["Games decided on points",pct(pointsOnly.length,out.length)],["Rival forced picks",avg(out.map(x=>x.events.rivalForced)).toFixed(2)+" / game"],["Rival non-forced picks (random)",avg(out.map(x=>x.events.rivalChoices)).toFixed(2)+" / game"],["Win rate AI A/B (excluding draws)",`${fmtPct(pA)} / ${fmtPct(pB)}`],["Delta B-A and 95% band",`${fmtPct(delta)} (±${fmtPct(ci95)})`],["Statistical reading",significance]]);
 renderRows(document.getElementById("vpTable"),[["Military VP (♠)",avg(pointsOnly.map(x=>x.score.military[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.military[1])).toFixed(2)],["Food VP (♣)",avg(pointsOnly.map(x=>x.score.food[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.food[1])).toFixed(2)],["Technology VP (♥)",avg(pointsOnly.map(x=>x.score.tech[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.tech[1])).toFixed(2)],["Culture VP (♦)",avg(pointsOnly.map(x=>x.score.culture[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.culture[1])).toFixed(2)],["Calamity VP (A: 1+K, B: none)",avg(pointsOnly.map(x=>x.score.calamity[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.calamity[1])).toFixed(2)],["Average Swords",avg(pointsOnly.map(x=>x.score.swords[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.swords[1])).toFixed(2)],["Average Tech Sequences",avg(pointsOnly.map(x=>x.score.breakthrough[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.breakthrough[1])).toFixed(2)]]);
 statusEl.textContent=`Completed: ${n} games.`; runBtn.disabled=false;}
runBtn.addEventListener("click",runBatch);
statusEl.textContent="Ready. Solo-mode statistical core loaded.";
})();
