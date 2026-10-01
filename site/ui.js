'use strict';
const $=id=>document.getElementById(id),fmt=n=>n.toLocaleString('en-GB',{maximumFractionDigits:3});
let input=Gasoline.family(5),custom=false,result,day=1,timer=null;
const text=(id,s)=>$(id).textContent=s;
function stop(){if(timer)clearInterval(timer);timer=null;text('play','Play decisions');}
function svgStart(w,h,label){return '<svg viewBox="0 0 '+w+' '+h+'" role="img" aria-label="'+label+'"><title>'+label+'</title>';}
function inventory(){
 const t=result.trace,opt=input.optimal?Gasoline.trace(input.optimal,input.y):null;
 const w=1000,h=300,left=45,right=24,top=23,bottom=36,max=Math.max(result.bound,t.capacity,opt?opt.capacity:0,1);
 const X=i=>left+i*(w-left-right)/(t.points.length-1),Y=v=>h-bottom-v*(h-top-bottom)/max;
 let s=svgStart(w,h,'Inventory trace, algorithm capacity '+result.capacity+(opt?', optimal capacity '+opt.capacity:''));
 for(let j=0;j<=4;j++){const v=max*j/4;s+='<line x1="'+left+'" y1="'+Y(v)+'" x2="'+(w-right)+'" y2="'+Y(v)+'" stroke="#d4ddd7"/><text x="'+(left-8)+'" y="'+(Y(v)+4)+'" text-anchor="end">'+fmt(v)+'</text>';}
 s+='<rect x="'+X((day-1)*2)+'" y="'+top+'" width="'+Math.max(2,X(day*2)-X((day-1)*2))+'" height="'+(h-top-bottom)+'" fill="#cb541e" opacity=".08"/>';
 const path=(p,A,limit=p.length)=>p.slice(0,limit).map((v,i)=>(i?'L':'M')+X(i)+','+Y(v-A)).join(' ');
 if(opt)s+='<path d="'+path(opt.points,opt.A)+'" fill="none" stroke="#087f79" stroke-width="2.5" opacity=".6"/>';
 s+='<path d="'+path(t.points,t.A)+'" fill="none" stroke="#c2cac4" stroke-width="2"/><path d="'+path(t.points,t.A,day*2+1)+'" fill="none" stroke="#cb541e" stroke-width="3"/>';
 for(const i of [day*2-1,day*2])s+='<circle cx="'+X(i)+'" cy="'+Y(t.points[i]-t.A)+'" r="4" fill="#cb541e"/>';
 const stride=Math.max(1,Math.ceil(input.y.length/14));for(let j=1;j<=input.y.length;j++)if(j===1||j===input.y.length||j%stride===0)s+='<text x="'+X(j*2)+'" y="'+(h-12)+'" text-anchor="middle">'+j+'</text>';
 s+='<text x="'+left+'" y="'+(h-12)+'">Day</text></svg>';$('traceChart').innerHTML=s;
}
function scorePlot(st){
 const both=st.candidates.length===2,h=result.h;
 if(!both){$('scoreChart').innerHTML='<p class="callout">Only delivery size '+st.chosen+' remains.</p>';text('roundingText','The remaining total forces this delivery. There is no rounding choice, and the fractional LP value cannot increase.');return;}
 const f=z=>Math.max(st.F,st.u-z,st.v+z)+1;
 const low=Math.max(0,Math.min(f(0),f(h),f(Math.max(0,Math.min(h,(st.u-st.v)/2))))-2);
 const high=Math.max(result.bound,f(0),f(h))+1,w=430,H=235;
 const X=z=>42+z/h*(w-66),Y=v=>H-38-(v-low)/(high-low)*(H-62);
 let s=svgStart(w,H,'Exact fractional completion score as delivery varies from 1 to '+result.K);
 for(let j=0;j<=3;j++){const v=low+(high-low)*j/3;s+='<line x1="42" x2="'+(w-24)+'" y1="'+Y(v)+'" y2="'+Y(v)+'" stroke="#e0e5e0"/><text x="34" y="'+(Y(v)+4)+'" text-anchor="end">'+fmt(v)+'</text>';}
 s+='<line x1="42" x2="'+(w-24)+'" y1="'+Y(result.bound)+'" y2="'+Y(result.bound)+'" stroke="#9d6549" stroke-dasharray="4 4"/><text x="'+(w-25)+'" y="'+(Y(result.bound)-7)+'" text-anchor="end">Proved bound '+result.bound+'</text>';
 const pts=[];for(let j=0;j<=60;j++){const z=h*j/60;pts.push((j?'L':'M')+X(z)+','+Y(f(z)));}
 s+='<path d="'+pts.join(' ')+'" fill="none" stroke="#087f79" stroke-width="2.5"/>';
 for(const z of [0,h])s+='<circle cx="'+X(z)+'" cy="'+Y(f(z))+'" r="5" fill="'+(st.chosen===z+1?'#cb541e':'#728780')+'"/><text x="'+X(z)+'" y="'+(H-17)+'" text-anchor="middle">'+(z+1)+'</text>';
 s+='<text x="'+(w/2)+'" y="'+(H-2)+'" text-anchor="middle">Next delivery size</text></svg>';
 $('scoreChart').innerHTML=s;
 const z=Math.max(0,Math.min(h,(st.u-st.v)/2)),min=f(z),chosen=st.candidates.find(c=>c.q===st.chosen).score;
 text('roundingText','The fractional LP can reach '+fmt(min)+'. Choosing the actual delivery '+st.chosen+' leaves LP value '+chosen+'. '+(chosen>min?'This fixing raises the lower bound by '+fmt(chosen-min)+'.':'This fixing does not raise the LP lower bound.'));
}
function showDay(){
 day=Math.max(1,Math.min(day,result.steps.length));$('day').value=day;text('dayLabel',day+' / '+result.steps.length);
 $('prev').disabled=day===1;$('next').disabled=day===result.steps.length;
 const st=result.steps[day-1],tied=st.candidates.length===2&&st.candidates[0].score===st.candidates[1].score;
 text('decisionTitle','Deliver '+st.chosen+', then consume '+st.demand);
 text('decisionText',st.candidates.length===1?'Only one delivery size is still available.':tied?'Both choices have LP score '+st.candidates[0].score+'. The selected tie rule chooses '+st.chosen+'.':'The smaller LP score selects delivery '+st.chosen+'. The tie rule does not affect this decision.');
 const scale=Math.max(result.bound,...st.candidates.map(c=>c.score));
 $('choices').innerHTML=st.candidates.map(c=>'<div class="choice '+(c.q===st.chosen?'selected':'')+'"><div><span>Delivery '+c.q+(c.q===st.chosen?' · chosen':'')+'</span><strong>LP '+c.score+'</strong></div><div class="bar"><i style="width:'+(100*c.score/scale)+'%"></i></div></div>').join('');
 inventory();scorePlot(st);
}
function render(){
 result=Gasoline.solve(input.x,input.y,$('policy').value);$('day').max=result.steps.length;$('k').disabled=custom;
 text('kLabel',result.K);text('capacity',result.capacity);text('bound',result.bound);
 const lower=Math.max(result.initialLP,result.K,...input.y);
 text('optLabel',custom?'Lower bound on optimum':'Optimal capacity');text('optimum',custom?lower:result.K);
 text('optNote',custom?'LP, largest demand and largest delivery':'Certified by a matching schedule');
 text('costNote',input.y.length+' days · initial LP '+result.initialLP);
 text('ratio',custom?'Ratio is at most '+fmt(result.capacity/lower):'Actual ratio '+fmt(result.capacity/result.K)+' / bound '+fmt(2-2/result.K));
 $('optimalLegend').hidden=custom;
 text('xList',input.x.join(', '));text('yList',input.y.join(', '));text('qList',result.order.join(', '));showDay();
}
$('k').addEventListener('input',()=>{stop();custom=false;input=Gasoline.family(Number($('k').value));render();});
$('policy').addEventListener('change',()=>{stop();render();});
$('day').addEventListener('input',()=>{stop();day=Number($('day').value);showDay();});
$('prev').onclick=()=>{stop();day--;showDay();};$('next').onclick=()=>{stop();day++;showDay();};
$('play').onclick=()=>{if(timer){stop();return;}if(day===result.steps.length)day=0;text('play','Pause');timer=setInterval(()=>{day++;showDay();if(day===result.steps.length)stop();},900);};
$('reset').onclick=()=>{stop();custom=false;$('k').value=5;$('policy').value='original';input=Gasoline.family(5);day=1;text('error','');render();};
$('customApply').onclick=()=>{stop();try{const parse=id=>$(id).value.trim().split(/[\s,;]+/).filter(Boolean).map(Number);const next={x:parse('customX'),y:parse('customY')};Gasoline.solve(next.x,next.y,$('policy').value);input=next;custom=true;day=1;text('error','');render();}catch(e){text('error',e.message);}};
render();

$('smallFailure').onclick=()=>{stop();custom=false;input={x:[1,1,1,5,5,5],y:[2,2,3,5,4,2],optimal:[5,1,1,5,5,1]};$('k').value=5;$('policy').value='small';day=1;render();$('labTitle').scrollIntoView({behavior:window.matchMedia('(prefers-reduced-motion: reduce)').matches?'auto':'smooth',block:'start'});};
