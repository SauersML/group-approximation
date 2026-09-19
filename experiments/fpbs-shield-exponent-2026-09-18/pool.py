import sys,glob,math
# pool per-sample digit lines; digits small->large scales; scales = NMIN*2^i
def load(pat,nmin=8):
    rows=[]
    for f in sorted(glob.glob(pat)):
        lines=open(f).read().split('\n')
        if not any(l.startswith('# N=') for l in lines): continue  # unfinished
        L=[l.split()[2] for l in lines if l.startswith('S ')]
        rows+=L
    return rows
def stats(rows,nmin=8,NB=20):
    ns=len(rows[0]); T=len(rows)
    out=[]
    for k in range(ns):
        n=nmin<<k
        def est(rs):
            D=sum(int(r[k])&1 for r in rs)/len(rs)
            H=sum((int(r[k])>>1)&1 for r in rs)/len(rs)
            I=sum((int(r[k])>>2)&1 for r in rs)/len(rs)
            if k>0:
                pd=sum(int(r[k-1])&1 for r in rs); jd=sum((int(r[k-1])&1)*(int(r[k])&1) for r in rs)
                ph=sum((int(r[k-1])>>1)&1 for r in rs); jh=sum(((int(r[k-1])>>1)&1)*((int(r[k])>>1)&1) for r in rs)
                pi=sum((int(r[k-1])>>2)&1 for r in rs); ji=sum(((int(r[k-1])>>2)&1)*((int(r[k])>>2)&1) for r in rs)
                sD=-math.log2(jd/pd) if jd else float('nan'); sH=-math.log2(jh/ph) if jh else float('nan'); sI=-math.log2(ji/pi) if ji else float('nan')
            else: sD=sH=sI=float('nan')
            return [D,H,I,sD,sH,sI]
        full=est(rows)
        bs=[rows[b::NB] for b in range(NB)]
        jk=[est([r for i,r in enumerate(rows) if i%NB!=b]) for b in range(NB)]
        errs=[math.sqrt((NB-1)/NB*sum((j[q]-full[q])**2 for j in jk)) for q in range(6)]
        out.append((n,full,errs))
    return T,out
for pat in sys.argv[1:]:
    rows=load(pat)
    if not rows: continue
    T,out=stats(rows)
    print("#",pat,"samples",T)
    print("#  n    Phi(err)            half(err)           PI(err)            slopeD(err)      slopeHalf(err)   slopePI(err)")
    for n,f,e in out:
        print("%5d "%n+" ".join("%.4f(%.4f)"%(f[q],e[q]) for q in range(6)))
