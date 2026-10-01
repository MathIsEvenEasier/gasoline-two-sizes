'use strict';
(function(root){
function family(K){const h=K-1,x=[],y=[2],optimal=[];for(let j=0;j<h-1;j++){x.push(K,1);optimal.push(1,K);}x.push(K);optimal.push(K);for(let j=1;j<h-1;j++)y.push(h-j,j+2);y.push(K,h);return{x,y,optimal};}
function trace(q,y){let s=0,A=0,B=0,points=[0];for(let i=0;i<q.length;i++){s+=q[i];B=Math.max(B,s);points.push(s);s-=y[i];A=Math.min(A,s);points.push(s);}return{points,A,B,capacity:B-A};}
function solve(x,y,policy='original'){
 if(!x.length||x.length!==y.length||x.length>200)throw Error('Use equally long lists with 1–200 entries.');
 if([...x,...y].some(v=>!Number.isSafeInteger(v)||v<1||v>1000000))throw Error('Every entry must be a positive integer no larger than 1,000,000.');
 const K=Math.max(...x),h=K-1,n=x.length,d=y.map(v=>v-1);
 if(x.some(v=>v!==1&&v!==K))throw Error('Deliveries must have at most two sizes: 1 and K.');
 if(x.reduce((a,b)=>a+b,0)!==y.reduce((a,b)=>a+b,0))throw Error('Total deliveries must equal total demand.');
 const D=Array(n+1).fill(0),T=D.slice(),V=D.slice();let total=0;
 for(let t=n-1;t>=0;t--){total+=d[t];D[t]=Math.max(0,d[t]-h+D[t+1]);T[t]=Math.max(T[t+1],total-h*(n-t-1));V[t]=Math.max(V[t+1],d[t]+D[t+1]);}
 const queues=new Map([...new Set(x)].map(v=>[v,{values:[],head:0}]));x.forEach((v,i)=>queues.get(v).values.push(i));
 let s=0,A=0,B=0;const order=[],steps=[],initialLP=Math.max(V[0],T[0]+D[0])+1;
 for(let t=0;t<n;t++){
  const R=d[t]+D[t+1],W=Math.max(B,T[t+1]),F=Math.max(V[t+1],W-A,R),u=W+R-s,v=s-A;
  const candidates=[...queues].filter(([,a])=>a.head<a.values.length).map(([q,a])=>({q,index:a.values[a.head],score:Math.max(F,u-(q-1),v+q-1)+1}));
  candidates.sort((a,b)=>a.score-b.score||(policy==='small'?a.q-b.q:policy==='large'?b.q-a.q:a.index-b.index));
  const chosen=candidates[0];steps.push({day:t+1,s,A,B,F,u,v,R,candidates:candidates.slice().sort((a,b)=>a.q-b.q),chosen:chosen.q,index:chosen.index,demand:y[t]});
  queues.get(chosen.q).head++;order.push(chosen.q);B=Math.max(B,s+chosen.q-1);s+=chosen.q-1-d[t];A=Math.min(A,s);
 }
 return{K,h,order,steps,capacity:B-A+1,initialLP,bound:K===1?1:initialLP+K-2,trace:trace(order,y)};
}
const api={family,trace,solve};if(typeof module!=='undefined')module.exports=api;root.Gasoline=api;
})(typeof window!=='undefined'?window:globalThis);
