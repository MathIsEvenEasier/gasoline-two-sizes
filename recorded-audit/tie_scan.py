"""Bounded Azure-only probe of always-small and always-large exact tie rules."""
import itertools,json,pathlib,random,time
from fast_algorithm import solve
from oracle import capacity,iterative_rounding
assert pathlib.Path('/run/mathiseasy-azure-verified').is_file()
rng=random.Random(20261001);start=time.monotonic();records={p:[] for p in ['small','large']};best={p:(1,1) for p in records};trials=0
while trials<10000 and time.monotonic()-start<30:
 n=rng.randrange(3,11);K=rng.randrange(3,17);m=rng.randrange(1,n)
 total=n+(K-1)*m
 cuts=sorted(rng.sample(range(1,total),n-1));y=[b-a for a,b in zip([0]+cuts,cuts+[total])]
 x=[1]*(n-m)+[K]*m
 opt=None;optorder=None
 for pos in itertools.combinations(range(n),m):
  q=[1]*n
  for i in pos:q[i]=K
  c=capacity(q,y)
  if opt is None or c<opt:opt,optorder=c,q
 for policy,xx in [('small',x),('large',x[::-1])]:
  f=solve(xx,y,True);num,den=best[policy]
  if f['capacity']*den>num*opt:
   slow=iterative_rounding(xx,y,True)
   assert f['steps']==slow['steps'] and f['capacity']==slow['capacity']
   best[policy]=(f['capacity'],opt)
   records[policy].append({'K':K,'x':xx,'y':y,'order':f['order'],'cost':f['capacity'],'optimal_order':optorder,'OPT':opt,'initial_lp':f['initial_lp']})
 trials+=1
pathlib.Path('tie-experiment.json').write_text(json.dumps({'status':'PASS','seed':20261001,'trials':trials,'seconds':time.monotonic()-start,'scope':'Random trials with repeats possible; n=3..10, K=3..16. Optima enumerate all binary orders. Every new record is checked by the independent cycle LP oracle. No universal guarantee follows from this experiment.','records':records},indent=2)+'\n')
