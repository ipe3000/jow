(function(){
const SUITS=["S","D","H","C"]; const RANKS=["A","2","3","4","5","6","7","8","9","10","J","Q","K"];
const DIAMOND_VP_AWARDS=[10,6,3];
const MILITARY_VP=5;
const CALAMITY_KING_THRESHOLD=3;
const CALAMITY_VP_PENALTY=-5;
const RANK_VAL=Object.fromEntries(RANKS.map((r,i)=>[r,i+1]));
const MASK13=(1<<13)-1;
const TABLEAU_MODEL={ancient:[{faceDown:false,xs:[2,4]},{faceDown:true,xs:[1.5,2.5,3.5,4.5]},{faceDown:false,xs:[0,1,2,3,4,5,6]},{faceDown:true,xs:[0.5,1.5,2.5,3.5,4.5,5.5]},{faceDown:false,xs:[1,2,3,4,5]}],modern:[{faceDown:false,xs:[2,5]},{faceDown:true,xs:[1.5,2.5,3.5,4.5,5.5]},{faceDown:false,xs:[0,1,2,3,4,5,6,7]},{faceDown:true,xs:[0.5,1.5,2.5,3.5,4.5,5.5,6.5]},{faceDown:false,xs:[1,2,3,4,5,6]}]};
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
 const tScale=1+0.2*(strength-1);
 const eps=Math.max(0.06,0.2-0.015*(strength-1));
 const modernSwapSimulations=Math.round(4+(strength-1)*0.8);
 return {strength,tScale,eps,modernSwapSimulations};
}
const DEFAULT_MC_CFG=mcSettings(1);
const HEURISTIC_WEIGHT_FOOD=1.25;
const HEURISTIC_WEIGHT_TECH=0.9;
const HEURISTIC_WEIGHT_DIAMOND=0.9;
function makeFeat(){return {sw:0,cw:0,hMask:0,hAdj:0,dMask:0,dAdj:0};}
function cloneFeat(feat){return {...feat};}
const pct=(x,n)=>n?`${(100*x/n).toFixed(1)}%`:"0.0%"; const avg=a=>a.length?a.reduce((x,y)=>x+y,0)/a.length:0;
const fmtPct=v=>`${(100*v).toFixed(1)}%`;
function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}
function makeDeck(){const cards=[];let id=0; for(const s of SUITS){for(const r of RANKS){cards.push({id:id++,suit:s,rank:r});}} return cards;}
function ageOf(rank){return ["A","2","3","4","5","6"].includes(rank)?"ancient":"modern";}
function buildRows(model){let idx=0; return model.map((cfg,row)=>cfg.xs.map((gridX,col)=>({idx:idx++,row,col,gridX})));}
function buildCovering(rows){const total=rows.reduce((a,r)=>a+r.length,0), coveredBy=Array.from({length:total},()=>[]); for(let r=0;r<rows.length-1;r++){const upper=rows[r],lower=rows[r+1],map=new Map(lower.map(s=>[s.gridX,s.idx])); for(const slot of upper){const c1=map.get(slot.gridX-0.5),c2=map.get(slot.gridX+0.5); if(c1!==undefined) coveredBy[slot.idx].push(c1); if(c2!==undefined) coveredBy[slot.idx].push(c2);}} return coveredBy;}
function buildCoveredByRev(coveredBy){const rev=Array.from({length:coveredBy.length},()=>[]); for(let i=0;i<coveredBy.length;i++) for(const c of coveredBy[i]) rev[c].push(i); return rev;}
function buildTableau(age,deck){const model=TABLEAU_MODEL[age], rows=buildRows(model), covering=buildCovering(rows), slots=[]; for(let row=0;row<model.length;row++){for(let col=0;col<model[row].xs.length;col++){slots.push({card:deck.pop(),removed:false,faceDown:model[row].faceDown,row,col});}} return {slots,coveredBy:covering,coveredByRev:buildCoveredByRev(covering)};}
function accessibility(T){const {slots,coveredBy}=T; return slots.map((s,i)=>!s.removed && !(coveredBy[i]||[]).some(c=>!slots[c].removed));}
function flipNew(slots,acc){for(let i=0;i<slots.length;i++) if(!slots[i].removed && slots[i].faceDown && acc[i]) slots[i].faceDown=false;}
function swords(cards){return cards.filter(c=>c.suit==="S").reduce((a,c)=>a+swordValue(c),0);}
function suitSequences(cards,suit){const owned=new Set(cards.filter(c=>c.suit===suit).map(c=>RANK_VAL[c.rank])); if(owned.size<2) return []; const present=i=>owned.has(i===0?13:i===14?1:i); if(owned.size===13) return [{length:13,high:13}]; const seq=[]; for(let i=1;i<=13;i++){if(!owned.has(i) || present(i-1)) continue; let len=1,cur=i; while(present(cur+1)){len++;cur=cur===13?1:cur+1;if(cur===i)break;} if(len>=2){let high=i; for(let k=0,cc=i;k<len;k++){if(cc===13) high=13; else if(high!==13 && cc>high) high=cc; cc=cc===13?1:cc+1;} seq.push({length:len,high});}} return seq;}
function breakthroughCount(cards){return suitSequences(cards,"H").length;}
function diamondSequences(cards){return suitSequences(cards,"D");}
function foodPower(cards){return cards.filter(c=>c.suit==="C").reduce((a,c)=>a+swordValue(c),0);}
function calamityPenalty(cards){const kings=cards.filter(c=>c.rank==="K").length; return kings>=CALAMITY_KING_THRESHOLD?CALAMITY_VP_PENALTY:0;}
function scoreFromCards(a,b){const sw=[swords(a),swords(b)], foodPowerByPlayer=[foodPower(a),foodPower(b)]; let vp=[0,0], military=[0,0], food=[0,0]; if(sw[0]>sw[1]) military=[MILITARY_VP,0]; else if(sw[1]>sw[0]) military=[0,MILITARY_VP]; if(foodPowerByPlayer[0]>foodPowerByPlayer[1]) food=[MILITARY_VP,0]; else if(foodPowerByPlayer[1]>foodPowerByPlayer[0]) food=[0,MILITARY_VP]; vp[0]+=military[0]+food[0]; vp[1]+=military[1]+food[1]; const techSeqs=[...suitSequences(a,"H").map(s=>({...s,o:0})),...suitSequences(b,"H").map(s=>({...s,o:1}))].sort((x,y)=>y.length-x.length||y.high-x.high); const tech=[0,0]; DIAMOND_VP_AWARDS.forEach((v,k)=>{if(techSeqs[k]){vp[techSeqs[k].o]+=v; tech[techSeqs[k].o]+=v;}}); const seqs=[...diamondSequences(a).map(s=>({...s,o:0})),...diamondSequences(b).map(s=>({...s,o:1}))].sort((x,y)=>y.length-x.length||y.high-x.high); const culture=[0,0]; DIAMOND_VP_AWARDS.forEach((v,k)=>{if(seqs[k]){vp[seqs[k].o]+=v; culture[seqs[k].o]+=v;}}); const calamity=[calamityPenalty(a),calamityPenalty(b)]; vp[0]+=calamity[0]; vp[1]+=calamity[1]; return {vp,military,food,tech,culture,calamity,swords:sw,breakthrough:[breakthroughCount(a),breakthroughCount(b)]};}
function checkSupremacy(S){const f0=S.players[0].feat, f1=S.players[1].feat; if(f0.sw-f1.sw>=7) return {winner:0,reason:"Military Supremacy"}; if(f1.sw-f0.sw>=7) return {winner:1,reason:"Military Supremacy"}; if(f0.cw-f1.cw>=7) return {winner:0,reason:"Food Supremacy"}; if(f1.cw-f0.cw>=7) return {winner:1,reason:"Food Supremacy"}; return null;}
function legalMoves(S){const acc=accessibility(S.tableau), res=[]; for(let i=0;i<S.tableau.slots.length;i++){const s=S.tableau.slots[i]; if(acc[i] && !s.removed && !s.faceDown) res.push(i);} return res;}
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
function bitOfRank(rank){return 1<<(RANK_VAL[rank]-1);}
function popcount13(x){x>>>=0; let c=0; while(x){x&=x-1;c++;} return c;}
function diamondAdjFromMask(mask){mask&=MASK13; const rot=((mask<<1)&MASK13)|(mask>>>12); return popcount13(mask&rot);}
function swordValue(card){const v=RANK_VAL[card.rank]; return (v<=9)?1:2;}
function updateFeat(feat,card){
 if(card.suit==="S") feat.sw+=swordValue(card);
 if(card.suit==="C") feat.cw+=swordValue(card);
 if(card.suit==="H"){feat.hMask|=bitOfRank(card.rank); feat.hAdj=diamondAdjFromMask(feat.hMask);}
 if(card.suit==="D"){feat.dMask|=bitOfRank(card.rank); feat.dAdj=diamondAdjFromMask(feat.dMask);}
}
function staticTakeValue(S,player,card){
 const f=S.players[player].feat;
 const dSw=(card.suit==="S")?swordValue(card):0;
 const dFood=(card.suit==="C")?swordValue(card):0;
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
 return dSw*1.25+dFood*HEURISTIC_WEIGHT_FOOD+dTech*HEURISTIC_WEIGHT_TECH+dDia*HEURISTIC_WEIGHT_DIAMOND;
}
function cheapEvalTake(S,player,idx){
 const slot=S.tableau.slots[idx]; if(!slot || slot.removed || slot.faceDown) return -Infinity;
 const card=slot.card;
 const me=S.players[player].feat, opp=S.players[1-player].feat;
 const dSw=(card.suit==="S")?swordValue(card):0;
 const dFood=(card.suit==="C")?swordValue(card):0;
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
 const deny=(card.suit==="S"?0.24:0)+(card.suit==="C"?0.24:0)+(card.suit==="H"?0.14:0)+(card.suit==="D"?0.14:0), pressure=Math.max(0,opp.sw-me.sw-5)*0.05+Math.max(0,opp.cw-me.cw-5)*0.05;
 const baseScore=dSw*1.25+dFood*HEURISTIC_WEIGHT_FOOD+dTech*HEURISTIC_WEIGHT_TECH+dDia*HEURISTIC_WEIGHT_DIAMOND+deny+pressure;
 let revealBonus=0;
 const rev=S.tableau.coveredByRev?.[idx]||[];
 for(const upperIdx of rev){
  const upper=S.tableau.slots[upperIdx];
  if(!upper || upper.removed) continue;
  const blockers=S.tableau.coveredBy[upperIdx]||[];
  const becomesAccessible=blockers.every(b=>b===idx || S.tableau.slots[b].removed);
  if(!becomesAccessible) continue;
  const w=upper.faceDown?0.35:0.18;
  revealBonus+=w*staticTakeValue(S,player,upper.card);
 }
 return baseScore+revealBonus;
}
function choosePlayoutMove(S,eps=0.2){
 const moves=legalMoves(S); if(!moves.length) return null;
 if(moves.length===1) return moves[0];
 if(Math.random()<eps) return moves[Math.floor(Math.random()*moves.length)];
 let best=moves[0],bestV=-Infinity; for(const idx of moves){const v=cheapEvalTake(S,S.current,idx); if(v>bestV){bestV=v;best=idx;}} return best;
}
function shouldUseJokerInPlayout(S){if(!(S.players[S.current].joker && S.picksLeftThisTurn===1)) return false; const moves=legalMoves(S); if(moves.length<2) return false; const p=S.current; if(canWinNowWithTwoPicks(S,p,moves,2)!==null) return true; if(S.age==="ancient" && remainingCardsThisAge(S)>6) return false; const vals=moves.map(i=>cheapEvalTake(S,p,i)).sort((a,b)=>b-a); const single=vals[0], two=vals[0]+0.85*vals[1]; const reserveBias=S.age==="ancient"?0.35:0.15; return two>single+(0.55+reserveBias);}
function cloneState(S){return {age:S.age,current:S.current,ended:S.ended,nextAgeFirst:S.nextAgeFirst,picksLeftThisTurn:S.picksLeftThisTurn,modernSwapStillAvailable:S.modernSwapStillAvailable,players:S.players.map(p=>({cards:p.cards.slice(),joker:p.joker,feat:cloneFeat(p.feat)})),tableau:{slots:S.tableau.slots.map(s=>({...s})),coveredBy:S.tableau.coveredBy,coveredByRev:S.tableau.coveredByRev},decks:{ancient:S.decks.ancient.slice(),modern:S.decks.modern.slice()},events:{jokerDouble:S.events.jokerDouble?S.events.jokerDouble.slice():[0,0],jokerDoubleByAge:S.events.jokerDoubleByAge?{ancient:S.events.jokerDoubleByAge.ancient.slice(),modern:S.events.jokerDoubleByAge.modern.slice()}:{ancient:[0,0],modern:[0,0]},modernSwap:S.events.modernSwap||0}};}
function finalReward(S,perspective){if(S.winner!==undefined) return S.winner===perspective?1:0; const sc=scoreFromCards(S.players[0].cards,S.players[1].cards).vp; if(sc[perspective]>sc[1-perspective]) return 1; if(sc[perspective]===sc[1-perspective]) return 0.5; return 0;}
function modernOpeningSwingScore(S,startPlayer){
 const C=cloneState(S);
 C.age="modern";
 C.current=startPlayer;
 C.picksLeftThisTurn=1;
 const hasReadyModernTableau=
  C.tableau &&
  Array.isArray(C.tableau.slots) &&
  C.tableau.slots.length===TABLEAU_MODEL.modern.reduce((n,row)=>n+row.xs.length,0) &&
  C.tableau.slots.every(s=>s && s.card);
 if(!hasReadyModernTableau) C.tableau=buildTableau("modern",C.decks.modern);

 const openerMoves=legalMoves(C);
 if(!openerMoves.length) return 0;

 let openerBest=-Infinity, openerBestIdx=openerMoves[0];
 for(const idx of openerMoves){
  const v=cheapEvalTake(C,startPlayer,idx);
  if(v>openerBest){openerBest=v; openerBestIdx=idx;}
 }

 // Stimiamo la perdita di opportunità: se parto secondo, l'avversario toglie
 // la carta migliore tra quelle disponibili subito in Età Moderna.
 applyTake(C,openerBestIdx);
 const responderMoves=legalMoves(C);
 let responderBest=0;
 if(responderMoves.length){
  responderBest=-Infinity;
  for(const idx of responderMoves) responderBest=Math.max(responderBest,cheapEvalTake(C,1-startPlayer,idx));
  if(!isFinite(responderBest)) responderBest=0;
 }

 return openerBest-responderBest;
}
function chooseModernSwap(S,nextFirst,mcCfg=DEFAULT_MC_CFG){
 const second=1-nextFirst; if(!S.players[second].joker) return nextFirst;
 const noSwap=cloneState(S); noSwap.age="modern"; noSwap.current=nextFirst; noSwap.picksLeftThisTurn=1; noSwap.tableau=buildTableau("modern",noSwap.decks.modern); noSwap.modernSwapStillAvailable=true;
 const swap=cloneState(S); swap.players[second].joker=false; swap.age="modern"; swap.current=second; swap.picksLeftThisTurn=1; swap.tableau=buildTableau("modern",swap.decks.modern); swap.modernSwapStillAvailable=true;
 const sims=Math.max(1,mcCfg.modernSwapSimulations||4);
 let evNo=0,evYes=0; for(let i=0;i<sims;i++){evNo+=randomPlayout(cloneState(noSwap),second,mcCfg); evYes+=randomPlayout(cloneState(swap),second,mcCfg);} evNo/=sims; evYes/=sims;
 const openingNo=modernOpeningSwingScore(noSwap,second);
 const openingYes=modernOpeningSwingScore(swap,second);
 const openingDelta=(openingYes-openingNo)*0.025;
 if(evYes+openingDelta>evNo+0.03){S.players[second].joker=false; S.events.modernSwap++; return second;} return nextFirst;
}
function advanceAge(S,mcCfg=DEFAULT_MC_CFG){if(S.age==="ancient"){const start=chooseModernSwap(S,S.nextAgeFirst,mcCfg); S.modernSwapStillAvailable=true; S.current=start; S.picksLeftThisTurn=1; S.age="modern"; S.tableau=buildTableau("modern",S.decks.modern); return;} S.ended=true;}
function applyTake(S,idx,mcCfg=DEFAULT_MC_CFG){const slot=S.tableau.slots[idx]; slot.removed=true; S.players[S.current].cards.push(slot.card); updateFeat(S.players[S.current].feat,slot.card); S.picksLeftThisTurn=Math.max(0,S.picksLeftThisTurn-1); flipNew(S.tableau.slots,accessibility(S.tableau)); const sup=checkSupremacy(S); if(sup){S.ended=true; S.winBy=sup.reason; S.winner=sup.winner; return;} if(S.age==="modern" && S.modernSwapStillAvailable) S.modernSwapStillAvailable=false; if(S.tableau.slots.every(s=>s.removed)) advanceAge(S,mcCfg); else if(S.picksLeftThisTurn<=0){S.picksLeftThisTurn=1; S.current=1-S.current;}}
function randomPlayout(S,perspective=S.current,mcCfg=DEFAULT_MC_CFG){let guard=600; while(!S.ended && guard-->0){const moves=legalMoves(S); if(!moves.length){S.picksLeftThisTurn=1; S.current=1-S.current; continue;} if(shouldUseJokerInPlayout(S)){S.players[S.current].joker=false;S.picksLeftThisTurn=2;} const idx=choosePlayoutMove(S,mcCfg.eps); if(idx===null){S.picksLeftThisTurn=1;S.current=1-S.current;continue;} applyTake(S,idx,mcCfg);} return finalReward(S,perspective);}
function chooseMoveUcb(S,moves,mcCfg,K=3){
 const ordered=moves.map(i=>({idx:i,v:cheapEvalTake(S,S.current,i)})).sort((a,b)=>b.v-a.v);
 const cand=ordered.slice(0,Math.min(K,ordered.length)).map(x=>x.idx);
 if(moves.length>cand.length && Math.random()<0.1){const extra=moves.filter(m=>!cand.includes(m)); if(extra.length) cand.push(extra[Math.floor(Math.random()*extra.length)]);}
 const left=S.tableau.slots.reduce((n,s)=>n+(!s.removed?1:0),0);
 let T=S.age==="ancient"?8:12; if(left<=10) T=18; if(left<=6) T=24;
 T=Math.max(1,Math.round(T*mcCfg.tScale));
 const stats=new Map(cand.map(i=>[i,{n:0,w:0}]));
 let total=0;
 for(let t=0;t<T;t++){
  const idx=ucbSelect(stats,++total,0.9);
  const C=cloneState(S); applyTake(C,idx,mcCfg);
  const r=randomPlayout(C,S.current,mcCfg);
  const st=stats.get(idx); st.n++; st.w+=r;
 }
 let best=cand[0],bestV=-Infinity;
 for(const [idx,st] of stats.entries()){const v=st.w/Math.max(1,st.n); if(v>bestV){bestV=v;best=idx;}}
 return best;
}
function bestSingleValue(S,moves){
 let best=-Infinity;
 for(const i of moves) best=Math.max(best,cheapEvalTake(S,S.current,i));
 return best;
}
function bestTwoPickValue(S,moves){
 const p=S.current;
 const firstCand=moves
  .map(i=>({i,v:cheapEvalTake(S,p,i)}))
  .sort((a,b)=>b.v-a.v)
  .slice(0,3);

 let best=-Infinity;
 for(const {i:first,v:v1} of firstCand){
  const C=cloneState(S);
  C.players[p].joker=false;
  C.picksLeftThisTurn=2;

  applyTake(C,first);

  const m2=legalMoves(C);
  let v2=0;
  if(m2.length){
   v2=-Infinity;
   for(const j of m2) v2=Math.max(v2,cheapEvalTake(C,p,j));
   if(!isFinite(v2)) v2=0;
  }

  best=Math.max(best,v1+0.9*v2);
 }
 return best;
}
function remainingCardsThisAge(S){
 let n=0;
 for(const sl of S.tableau.slots) if(!sl.removed) n++;
 return n;
}
function jokerDecisionThreshold(S,player=S.current){
 const left=remainingCardsThisAge(S);
 let threshold=0.06;
 if(S.age==="ancient"){
  if(left>12) threshold=0.09;
  else if(left>7) threshold=0.07;
  else threshold=0.05;
  const t=Math.min(1,Math.max(0,left/18));
  const second=1-S.nextAgeFirst;
  threshold+=0.03+0.04*t;
  if(player===second) threshold+=0.02+0.03*t;
 }else{
  threshold=left>10?0.07:0.04;
 }
 return threshold;
}
function canWinNowWithOnePick(S,player=S.current,moves=legalMoves(S)){
 for(const idx of moves){
  const C=cloneState(S);
  C.current=player;
  C.picksLeftThisTurn=1;
  applyTake(C,idx);
  if(C.ended && C.winner===player) return idx;
 }
 return null;
}
function canWinNowWithTwoPicks(S,player=S.current,moves=legalMoves(S),firstCap=4){
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

  applyTake(C,first);
  if(C.ended && C.winner===player) return first;

  const m2=legalMoves(C);
  for(const second of m2){
   const D=cloneState(C);
   applyTake(D,second);
   if(D.ended && D.winner===player) return first;
  }
 }
 return null;
}
function opponentCanWinImmediately(S,opponent){
 const T=cloneState(S);
 T.current=opponent;
 T.picksLeftThisTurn=1;
 if(canWinNowWithOnePick(T,opponent)!==null) return true;
 if(T.players[opponent].joker && canWinNowWithTwoPicks(T,opponent,legalMoves(T),3)!==null) return true;
 return false;
}
function findSafeSingleMove(S,player=S.current,moves=legalMoves(S)){
 const ordered=moves
  .map(i=>({i,v:cheapEvalTake(S,player,i)}))
  .sort((a,b)=>b.v-a.v)
  .map(x=>x.i);
 for(const idx of ordered){
  const C=cloneState(S);
  C.current=player;
  C.picksLeftThisTurn=1;
  applyTake(C,idx);
  if(C.ended && C.winner===player) return idx;
  if(!opponentCanWinImmediately(C,1-player)) return idx;
 }
 return null;
}
function findSafeJokerFirstMove(S,player=S.current,moves=legalMoves(S)){
 if(!(S.players[player].joker && S.picksLeftThisTurn===1)) return null;
 const firstMoves=moves
  .map(i=>({i,v:cheapEvalTake(S,player,i)}))
  .sort((a,b)=>b.v-a.v)
  .slice(0,4)
  .map(x=>x.i);
 for(const first of firstMoves){
  const C=cloneState(S);
  C.current=player;
  C.players[player].joker=false;
  C.picksLeftThisTurn=2;
  applyTake(C,first);
  if(C.ended && C.winner===player) return first;

  const secondMoves=legalMoves(C)
   .map(i=>({i,v:cheapEvalTake(C,player,i)}))
   .sort((a,b)=>b.v-a.v)
   .slice(0,4)
   .map(x=>x.i);

  for(const second of secondMoves){
   const D=cloneState(C);
   applyTake(D,second);
   if(D.ended && D.winner===player) return first;
   if(!opponentCanWinImmediately(D,1-player)) return first;
  }
 }
 return null;
}
function maybeUseJokerNow(S,moves){
 if(!(S.players[S.current].joker && S.picksLeftThisTurn===1 && moves.length>=2)) return false;
 const p=S.current;
 if(canWinNowWithOnePick(S,p,moves)!==null) return false;
 if(canWinNowWithTwoPicks(S,p,moves,4)!==null) return true;
 const safeNoJ=findSafeSingleMove(S,p,moves);
 if(safeNoJ===null){
  const safeWithJ=findSafeJokerFirstMove(S,p,moves);
  if(safeWithJ!==null) return true;
 }
 const v1=bestSingleValue(S,moves);
 const v2=bestTwoPickValue(S,moves);
 const threshold=jokerDecisionThreshold(S,p);
 return v2>v1+threshold;
}
function chooseMove(S,strategy,mcCfg){const moves=legalMoves(S); if(!moves.length) return null; if(moves.length===1) return moves[0]; if(strategy==="random") return moves[Math.floor(Math.random()*moves.length)]; if(strategy==="greedy"){let best=moves[0],bestV=-Infinity; for(const idx of moves){const v=cheapEvalTake(S,S.current,idx); if(v>bestV){bestV=v;best=idx;}} return best;}
 if(maybeUseJokerNow(S,moves)){S.players[S.current].joker=false; S.picksLeftThisTurn=2; S.events.jokerDouble[S.current]++; S.events.jokerDoubleByAge[S.age][S.current]++;}
 return chooseMoveUcb(S,legalMoves(S),mcCfg,3);}
function simulateOne(startPlayer,strA,strB,mcCfg){const base=shuffle(makeDeck()); const ancient=shuffle(base.filter(c=>ageOf(c.rank)==="ancient")); const modern=shuffle(base.filter(c=>ageOf(c.rank)==="modern"));
 const S={age:"ancient",nextAgeFirst:1-startPlayer,current:startPlayer,ended:false,decks:{ancient,modern},tableau:buildTableau("ancient",ancient),players:[{cards:[],joker:true,feat:makeFeat()},{cards:[],joker:true,feat:makeFeat()}],picksLeftThisTurn:1,modernSwapStillAvailable:false,events:{jokerDouble:[0,0],jokerDoubleByAge:{ancient:[0,0],modern:[0,0]},modernSwap:0}};
 let guard=1000; while(!S.ended && guard-->0){const strat=S.current===0?strA:strB; const mv=chooseMove(S,strat,mcCfg); if(mv===null){S.picksLeftThisTurn=1; S.current=1-S.current; continue;} applyTake(S,mv,mcCfg);} const score=scoreFromCards(S.players[0].cards,S.players[1].cards);
 const vpA=score.vp[0], vpB=score.vp[1]; const winner=S.winner!==undefined?(S.winner===0?"a":"b"):(vpA===vpB?"draw":(vpA>vpB?"a":"b")); const winBy=S.winBy || (winner==="draw"?"Points draw":"Points");
 return {vpA,vpB,margin:vpB-vpA,winner,winBy,score,events:S.events};}
function renderRows(tbody,rows){tbody.innerHTML=rows.map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td>${r[2]!==undefined?`<td>${r[2]}</td>`:""}</tr>`).join("");}
function renderHistogram(margins){const buckets=new Map(); for(let x=-20;x<=20;x+=4) buckets.set(`${x}..${x+3}`,0); buckets.set("<=-21",0); buckets.set(">=21",0); for(const m of margins){if(m<=-21)buckets.set("<=-21",buckets.get("<=-21")+1); else if(m>=21)buckets.set(">=21",buckets.get(">=21")+1); else {const b=Math.floor((m+20)/4),s=-20+b*4,key=`${s}..${s+3}`; buckets.set(key,buckets.get(key)+1);}} const total=Math.max(1,margins.length),maxN=Math.max(1,...buckets.values()); document.getElementById("marginHist").innerHTML=[...buckets.entries()].map(([k,v])=>`<div class="bar"><div>${k}</div><div class="track"><div class="fill" style="width:${Math.round(100*v/maxN)}%"></div></div><div>${(100*v/total).toFixed(1)}%</div></div>`).join("");}
async function runBatch(){const n=Math.max(1,Math.min(10000,Number(document.getElementById("games").value)||1000)); const sA=document.getElementById("playerStrategy").value, sB=document.getElementById("aiStrategy").value, sm=document.getElementById("startMode").value, mcCfg=mcSettings(readMcStrength());
 runBtn.disabled=true; const out=[]; let lastUiTick=performance.now();
 for(let i=0;i<n;i++){
  const start=sm==="alternate"?(i%2):sm==="a"?0:1;
  out.push(simulateOne(start,sA,sB,mcCfg));
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
 const pointsOnly=out.filter(x=>x.winBy==="Points"||x.winBy==="Points draw");
 document.getElementById("kGames").textContent=String(out.length); document.getElementById("kAWin").textContent=pct(aWin,out.length); document.getElementById("kBWin").textContent=pct(bWin,out.length); document.getElementById("kDraw").textContent=pct(draw,out.length);
 const margins=out.map(x=>x.margin); renderHistogram(margins);
 renderRows(document.getElementById("scoreTable"),[["Average VP",avg(out.map(x=>x.vpA)).toFixed(2),avg(out.map(x=>x.vpB)).toFixed(2)],["Median VP",out.map(x=>x.vpA).sort((a,b)=>a-b)[Math.floor(out.length/2)],out.map(x=>x.vpB).sort((a,b)=>a-b)[Math.floor(out.length/2)]],["Average margin (B-A)",avg(margins).toFixed(2),"—"],["Supremacy wins",pct(out.filter(x=>x.winBy.includes("Supremacy") && x.winner==="a").length,out.length),pct(out.filter(x=>x.winBy.includes("Supremacy") && x.winner==="b").length,out.length)]]);
 renderRows(document.getElementById("eventTable"),[["Military Supremacy",pct(out.filter(x=>x.winBy==="Military Supremacy").length,out.length)],["Food Supremacy",pct(out.filter(x=>x.winBy==="Food Supremacy").length,out.length)],["Games decided on points",pct(pointsOnly.length,out.length)],["Wonder Extra Turn AI A",avg(out.map(x=>x.events.jokerDouble[0])).toFixed(2)+" / game"],["Wonder Extra Turn AI B",avg(out.map(x=>x.events.jokerDouble[1])).toFixed(2)+" / game"],["Wonder Extra Turn AI A — Ancient Age",avg(out.map(x=>x.events.jokerDoubleByAge.ancient[0])).toFixed(2)+" / game"],["Wonder Extra Turn AI A — Modern Age",avg(out.map(x=>x.events.jokerDoubleByAge.modern[0])).toFixed(2)+" / game"],["Wonder Extra Turn AI B — Ancient Age",avg(out.map(x=>x.events.jokerDoubleByAge.ancient[1])).toFixed(2)+" / game"],["Wonder Extra Turn AI B — Modern Age",avg(out.map(x=>x.events.jokerDoubleByAge.modern[1])).toFixed(2)+" / game"],["Wonder Seize Initiative (Modern Age)",pct(out.filter(x=>x.events.modernSwap>0).length,out.length)],["Win rate AI A/B (excluding draws)",`${fmtPct(pA)} / ${fmtPct(pB)}`],["Delta B-A and 95% band",`${fmtPct(delta)} (±${fmtPct(ci95)})`],["Statistical reading",significance]]);
 renderRows(document.getElementById("vpTable"),[["Military VP (♠)",avg(pointsOnly.map(x=>x.score.military[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.military[1])).toFixed(2)],["Food VP (♣)",avg(pointsOnly.map(x=>x.score.food[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.food[1])).toFixed(2)],["Technology VP (♥)",avg(pointsOnly.map(x=>x.score.tech[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.tech[1])).toFixed(2)],["Culture VP (♦)",avg(pointsOnly.map(x=>x.score.culture[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.culture[1])).toFixed(2)],["Calamity VP (3+ Kings)",avg(pointsOnly.map(x=>x.score.calamity[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.calamity[1])).toFixed(2)],["Average Swords",avg(pointsOnly.map(x=>x.score.swords[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.swords[1])).toFixed(2)],["Average Tech Sequences",avg(pointsOnly.map(x=>x.score.breakthrough[0])).toFixed(2),avg(pointsOnly.map(x=>x.score.breakthrough[1])).toFixed(2)]]);
 statusEl.textContent=`Completed: ${n} games.`; runBtn.disabled=false;}
runBtn.addEventListener("click",runBatch);
statusEl.textContent="Ready. Statistical core aligned with game rules.";
})();
