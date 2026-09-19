import json, subprocess, glob, os
R='/home/user/group-approximation'
C=R+'/experiments/bmw-census-left-orders-2026-09-17'
def show(p):
    try: return subprocess.run(['git','-C',R,'show','origin/main:'+p],capture_output=True,text=True,check=True).stdout
    except Exception: return None
pats=sorted(os.path.basename(f)[4:-6] for f in glob.glob(C+'/out_*.jsonl') if 'cx' not in f)
cert={}
for p in pats:
    s=set()
    for path in ['experiments/bmw-klein-chains-transposed-2026-09-17/chains_%s.json'%p,'experiments/bmw-klein-chains-2026-09-17/chains_census_%s.json'%p]:
        t=show(path)
        if t: s|=set(int(k) for k in json.loads(t))
    cert[p]=s
cert['50_30'].add(470); cert['41_30']|={80,113}; cert['52_30'].add(158); cert['31_30'].add(26); cert['31_31'].add(12)
out={}
tot=0
for p in pats:
    recs=[json.loads(l) for l in open(C+'/out_%s.jsonl'%p)]
    cand=[r for r in recs if r['finH'] is None or r['finV'] is None]
    rem=[r['idx'] for r in cand if r['idx'] not in cert[p]]
    sat=[r['idx'] for r in cand if r['idx'] not in cert[p] and all(v[0] for k,v in r.items() if k.startswith('R'))]
    out[p]=rem; tot+=len(rem)
    print(p,'classes',len(recs),'cand',len(cand),'cert',len(cert[p]&set(r['idx'] for r in cand)),'remaining',len(rem),'allSAT',sat[:10])
print('total',tot)
json.dump(out,open('remaining.json','w'))
