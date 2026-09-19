import sys, math
# karm.c output: 7 masks per sample, bit b <-> n = 8*2^b.
# cols: 0 A_UL, 1 A_LL, 2 A_UH, 3 A_LH, 4 D'(x>0), 5 D'(axis), 6 origin in I_n.
# Derived: 7 = A_UL&A_LL (sub-event of col 4), 8 = A_UH&A_LH (sub-event of col 5).
# Local slope at n = -log2 P(E_n)/P(E_{n/2}); errors: 20-block jackknife.
NAMES=["A_UL","A_LL","A_UH","A_LH","D'(pi/2)","D'(0)","0 in I","A_UL&A_LL","A_UH&A_LH"]
def jk(rows, f, B=20):
    m=len(rows); full=f(rows); vals=[]
    for b in range(B):
        sub=[r for k,r in enumerate(rows) if k*B//m!=b]; vals.append(f(sub))
    vals=[v for v in vals if v==v]
    mu=sum(vals)/len(vals); var=(len(vals)-1)/len(vals)*sum((v-mu)**2 for v in vals)
    return full, math.sqrt(var)
def cnt(R,bit,c): return sum((r[c]>>bit)&1 for r in R)
def prob(bit,c): return lambda R: cnt(R,bit,c)/len(R)
def slope(b0,b1,c):
    def f(R):
        a=cnt(R,b0,c); b=cnt(R,b1,c)
        return math.log2(a/b)/(b1-b0) if a and b else float('nan')
    return f
R=[]
for fn in sys.argv[1:]:
    for l in open(fn):
        if l.strip():
            r=list(map(int,l.split())); r+= [r[0]&r[1], r[2]&r[3]]; R.append(r)
nb=max(r[6] for r in R).bit_length()
nb=max(nb, max(r[4] for r in R).bit_length())
v1=sum(1 for r in R if r[7] & ~r[4]); v2=sum(1 for r in R if r[8] & ~r[5])
print(f"# files {sys.argv[1:]}; samples {len(R)}; inclusion violations A_UL&A_LL !=> D'(pi/2): {v1}, A_UH&A_LH !=> D'(0): {v2}")
# Duality checks: is D'(0) & {0 in I} equal to A_UH&A_LH, and D'(pi/2) & {0 in I} equal to A_UL&A_LL?
e0=sum(bin((r[5]&r[6])^r[8]).count('1') for r in R); e1=sum(bin((r[4]&r[6])^r[7]).count('1') for r in R)
print(f"# (sample,n) pairs with D'(0)&C != A_UH&A_LH: {e0};  with D'(pi/2)&C != A_UL&A_LL: {e1}")
for c in [0,1,2,3,7,8,4,5,6]:
    print(f"## {NAMES[c]}")
    for b in range(nb):
        p=jk(R,prob(b,c)); s=jk(R,slope(b-1,b,c)) if b else (float('nan'),0)
        print(f"   n={8<<b:4d}  P={p[0]:.4f}({p[1]:.4f})  local slope={s[0]:.4f}({s[1]:.4f})")
    if nb>=5:
        s=jk(R,slope(nb-4,nb-1,c)); print(f"   pooled slope n={8<<(nb-4)}->{8<<(nb-1)}: {s[0]:.4f}({s[1]:.4f})")
# Correlation diagnostics.  kappa_n = P(A&B) P(0 in I) / (P(A) P(B)): bounded in n <=> the two wedge
# arms are asymptotically independent given the one-arm event (joint exponent 2 alpha - 5/48).
# fill_n = P(A&B)/P(E): the fraction of the box event E carried by the two-arm sub-event.
def ratio(bit,cs,num):
    def f(R):
        p=[cnt(R,bit,c)/len(R) for c in cs]
        return (p[0]*p[1])/(p[2]*p[3]) if num else p[0]/p[1]
    return f
print("## correlation diagnostics")
for b in range(nb):
    k1=jk(R,ratio(b,[7,6,0,1],1)); k2=jk(R,ratio(b,[8,6,2,3],1))
    f1=jk(R,ratio(b,[7,4],0)); f2=jk(R,ratio(b,[8,5],0))
    print(f"   n={8<<b:4d}  kappa(UL,LL)={k1[0]:.3f}({k1[1]:.3f})  kappa(UH,LH)={k2[0]:.3f}({k2[1]:.3f})"
          f"  fill(pi/2)={f1[0]:.3f}({f1[1]:.3f})  fill(0)={f2[0]:.3f}({f2[1]:.3f})")
