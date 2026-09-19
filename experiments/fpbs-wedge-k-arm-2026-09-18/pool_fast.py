import sys, math
# karm.c mode 1 output: cols 0 A_UL, 1 A_LL, 2 A_UH, 3 A_LH, 4 A_UR, 5 A_LR, 6 origin in I_n; bit b <-> n=8*2^b.
# The four quadrant events have the same law (reflections x->-x, y->-y), as do the two half-plane events.
# Estimators: q_n = mean over the 4 quadrants, h_n = mean over the 2 halves; slopes -log2 ratio; 20-block jackknife.
# Also the joint two-arm events: QQ = UL&LL (and UR&LR), HH = UH&LH, with kappa = P(joint) P(C) / P(single)^2.
def jk(rows, f, B=20):
    m=len(rows); full=f(rows); vals=[]
    for b in range(B):
        sub=[r for k,r in enumerate(rows) if k*B//m!=b]; vals.append(f(sub))
    vals=[v for v in vals if v==v]
    mu=sum(vals)/len(vals); var=(len(vals)-1)/len(vals)*sum((v-mu)**2 for v in vals)
    return full, math.sqrt(var)
G={'quadrant':[0,1,4,5],'half':[2,3],'one-arm':[6],'QQ':['01','45'],'HH':['23']}
def p(R,bit,key):
    cs=G[key]; tot=0
    for c in cs:
        if isinstance(c,str): tot+=sum(((r[int(c[0])]&r[int(c[1])])>>bit)&1 for r in R)
        else: tot+=sum((r[c]>>bit)&1 for r in R)
    return tot/(len(cs)*len(R))
def sl(b0,b1,key): return lambda R: math.log2(p(R,b0,key)/p(R,b1,key))/(b1-b0)
R=[list(map(int,l.split())) for fn in sys.argv[1:] for l in open(fn) if l.strip()]
nb=max(r[6] for r in R).bit_length()
print(f"# files {sys.argv[1:]}; samples {len(R)}")
for key in ['quadrant','half','one-arm','QQ','HH']:
    print(f"## {key}")
    for b in range(nb):
        pr=jk(R,lambda X:p(X,b,key)); s=jk(R,sl(b-1,b,key)) if b else (float('nan'),0)
        print(f"   n={8<<b:4d}  P={pr[0]:.4f}({pr[1]:.4f})  local slope={s[0]:.4f}({s[1]:.4f})")
    for b0 in range(1,nb-1):
        s=jk(R,sl(b0,nb-1,key)); print(f"   pooled slope n={8<<b0}->{8<<(nb-1)}: {s[0]:.4f}({s[1]:.4f})")
print("## kappa = P(joint) P(C) / P(single)^2")
for b in range(nb):
    kq=jk(R,lambda X:p(X,b,'QQ')*p(X,b,'one-arm')/p(X,b,'quadrant')**2)
    kh=jk(R,lambda X:p(X,b,'HH')*p(X,b,'one-arm')/p(X,b,'half')**2)
    print(f"   n={8<<b:4d}  kappa_Q={kq[0]:.4f}({kq[1]:.4f})  kappa_H={kh[0]:.4f}({kh[1]:.4f})")
