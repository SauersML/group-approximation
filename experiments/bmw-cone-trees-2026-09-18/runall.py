# run dtree2 on every remaining class whose first UNSAT radius is Rsel; log one line per class
import json, subprocess, sys, os, time
C='/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
rem=json.load(open('remaining.json')); Rsel=sys.argv[1]; R=int(sys.argv[2]); ML=sys.argv[3]; TM=sys.argv[4]; log=sys.argv[5]
done=set()
if os.path.exists(log): done={(json.loads(l)['pat'],json.loads(l)['cls']) for l in open(log)}
pats=sys.argv[6:] or list(rem)
ONLY=None
if os.environ.get('ONLY'): ONLY={(json.loads(l)['pat'],json.loads(l)['cls']) for l in open(os.environ['ONLY']) if not json.loads(l)['ok']}
for p in pats:
    recs={json.loads(x)['idx']:json.loads(x) for x in open(C+'out_%s.jsonl'%p)}
    for i in rem[p]:
        if (p,i) in done: continue
        if ONLY is not None and (p,i) not in ONLY: continue
        r=recs[i]; first=[k for k,v in r.items() if k.startswith('R') and not v[0]]
        if not first or first[0]!=Rsel: continue
        t=time.time(); f='trees/tree_%s_%d.json'%(p,i)
        try:
            out=subprocess.run(['nice','-n','10','python3','dtree2.py','census_%s.json'%p,str(i),str(R),ML,TM]+([os.environ['SHORT']] if os.environ.get('SHORT') else []),capture_output=True,text=True,timeout=float(TM)+300).stdout
        except subprocess.TimeoutExpired: out='timeout'
        ok='"tree"' in out
        if ok: open(f,'w').write(out)
        lv=[json.loads(l) for l in out.splitlines() if l.startswith('{')]
        rec=dict(pat=p,cls=i,R=R,ok=ok,leaves=lv[0]['leaves'] if lv else None,sec=round(time.time()-t,1),msg=out.splitlines()[-1][:80] if out and not ok else '')
        open(log,'a').write(json.dumps(rec)+'\n')
