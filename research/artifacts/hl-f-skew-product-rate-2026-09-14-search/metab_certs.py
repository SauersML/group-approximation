# Deterministic capture of metabelian pairs attaining t = 2 d(R1) + d(R2) (sharpness), plus the reduced u2 word.
import itertools, random
R1='bAABaaBAba'; R2='bAAABaaaBAAbaa'; C='abAB'
def inv(P):
    Q=[0]*len(P)
    for i,x in enumerate(P): Q[x]=i
    return Q
def word(wd,A,B):
    M={'a':A,'A':inv(A),'b':B,'B':inv(B)}; cur=list(range(len(A)))
    for ch in reversed(wd):
        P=M[ch]; cur=[P[x] for x in cur]
    return cur
def moved(P): return sum(1 for i,x in enumerate(P) if i!=x)
def counts(A,B): return moved(word(R1,A,B)),moved(word(R2,A,B)),moved(word(C,A,B))
out=[]
# torus base Z/3 x Z/3, fibre Z/2: exhaustive over cocycles c,d in (Z/2)^9 x (Z/2)^9 would be 2^18=262144 -- fine
N,k=3,2
pts=[(x,y,i) for x in range(N) for y in range(N) for i in range(k)]; idx={p:j for j,p in enumerate(pts)}
best=None
for cbits in range(2**9):
    c=[(cbits>>j)&1 for j in range(9)]
    for dbits in range(2**9):
        d=[(dbits>>j)&1 for j in range(9)]
        A=[idx[((x+1)%N,y,(i+c[3*x+y])%k)] for (x,y,i) in pts]
        B=[idx[(x,(y+1)%N,(i+d[3*x+y])%k)] for (x,y,i) in pts]
        m1,m2,mc=counts(A,B)
        if mc and (best is None or max(m1,m2)*best[2] < max(best[0],best[1])*mc):
            best=(m1,m2,mc,A,B,c,d)
m1,m2,mc,A,B,c,d=best
print('torus3xZ2 exhaustive: min max-ratio', f'{max(m1,m2)}/{mc}', 'm1,m2,mc=',m1,m2,mc,'tight:',mc==2*m1+m2)
print('A=' + ','.join(map(str,A))); print('B=' + ','.join(map(str,B))); print('c=',c,'d=',d)
out.append(('torus3xZ2',m1,m2,mc,A,B))
# Z/2 wr Z/5 exhaustive
k,m=2,5
pts=[(i,x) for i in range(m) for x in range(k)]; idx={p:j for j,p in enumerate(pts)}
elems=[]
for s in range(m):
    for cfg in itertools.product(range(k),repeat=m):
        elems.append([idx[((i+s)%m,(x+cfg[i])%k)] for (i,x) in pts])
bestsum=None
for A in elems:
    for B in elems:
        m1,m2,mc=counts(A,B)
        if mc and (bestsum is None or (m1+m2)*bestsum[2] < (bestsum[0]+bestsum[1])*mc):
            bestsum=(m1,m2,mc,A,B)
m1,m2,mc,A,B=bestsum
print('Z2wrZ5 exhaustive: min sum-ratio', f'{m1+m2}/{mc}', 'm1,m2,mc=',m1,m2,mc,'tight:',mc==2*m1+m2)
print('A=' + ','.join(map(str,A))); print('B=' + ','.join(map(str,B)))
out.append(('Z2wrZ5',m1,m2,mc,A,B))
with open('/private/tmp/claude-501/-Users-user-nonsofic-existence/829306b2-1fe5-42c3-a312-35bcc8c1425f/scratchpad/skewrate/metab_certs.txt','w') as f:
    for tag,m1,m2,mc,A,B in out:
        f.write(f'{tag} m1={m1} m2={m2} mc={mc}\nA=' + ','.join(map(str,A)) + '\nB=' + ','.join(map(str,B)) + '\n')
# u2 = C * (a^2 R2 a^-2) (a R1^-1 a^-1) (a^2 R1^-1 a^-2), freely reduced
def invw(w): return ''.join(ch.swapcase() for ch in reversed(w))
def reduce(w):
    st=[]
    for ch in w:
        if st and st[-1]==ch.swapcase(): st.pop()
        else: st.append(ch)
    return ''.join(st)
u2=reduce(C + 'aa'+R2+'AA' + 'a'+invw(R1)+'A' + 'aa'+invw(R1)+'AA')
print('u2 =',u2,'length',len(u2))
