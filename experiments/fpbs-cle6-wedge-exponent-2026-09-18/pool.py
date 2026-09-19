import sys, math
# Each line: Dmask Pmask, bit b <-> n = 8*2^b. Local slope at n = -log2 P(D_n | D_{n/2}).
# Errors: 20-block jackknife.
def jk(rows, f, B=20):
    m=len(rows); full=f(rows); vals=[]
    for b in range(B):
        sub=[r for k,r in enumerate(rows) if k*B//m!=b]; vals.append(f(sub))
    vals=[v for v in vals if v==v]
    mu=sum(vals)/len(vals); var=(len(vals)-1)/len(vals)*sum((v-mu)**2 for v in vals)
    return full, math.sqrt(var)
def prob(bit,col): return lambda R: sum((r[col]>>bit)&1 for r in R)/len(R)
def slope(bit,col):
    def f(R):
        a=sum((r[col]>>(bit-1))&1 for r in R); b=sum((r[col]>>bit)&1 for r in R)
        return -math.log2(b/a) if a and b else float('nan')
    return f
for fn in sys.argv[1:]:
    R=[tuple(map(int,l.split())) for l in open(fn) if l.strip()]
    nb=max(r[0]|r[1] for r in R).bit_length()
    viol=sum(1 for r in R for b in range(1,nb) if (r[0]>>b)&1 and not (r[0]>>(b-1))&1)
    print(f"# {fn}: samples {len(R)}, monotonicity violations (D_n true, D_(n/2) false): {viol}")
    print("#    n   P(D_n)          P(0 in I_n)     slopeD          slopePI")
    for b in range(nb):
        pd=jk(R,prob(b,0)); pp=jk(R,prob(b,1))
        s=jk(R,slope(b,0)) if b else (float('nan'),0); t=jk(R,slope(b,1)) if b else (float('nan'),0)
        print(f"{8<<b:6d} {pd[0]:.4f}({pd[1]:.4f}) {pp[0]:.4f}({pp[1]:.4f}) {s[0]:.4f}({s[1]:.4f}) {t[0]:.4f}({t[1]:.4f})")
