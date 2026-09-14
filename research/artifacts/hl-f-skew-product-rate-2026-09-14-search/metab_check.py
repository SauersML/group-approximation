# (1) Verify c = abAB and (a^2 R1 a^-2)(a R1 a^-1)(a^2 R2 a^-2)^-1 agree in the Magnus representation
#     of F_2/F_2'' (faithful): a -> [[s, e1],[0,1]], b -> [[t, e2],[0,1]], entries in Z[Z^2] and the
#     free Z[Z^2]-module on e1, e2.
# (2) Check d(AB,BA) <= 2 d(R1,1) + d(R2,1) on metabelian permutation pairs (affine maps mod p,
#     and lamplighter-type pairs), and report the smallest ratio seen.
import random, itertools
from collections import defaultdict
def padd(p,q,c=1):
    r=defaultdict(int,p)
    for k,v in q.items(): r[k]+=c*v
    return {k:v for k,v in r.items() if v}
def pmul(p,q):
    r=defaultdict(int)
    for (i,j),v in p.items():
        for (k,l),w in q.items(): r[(i+k,j+l)]+=v*w
    return {k:v for k,v in r.items() if v}
# element of the Magnus group: (monomial (i,j), module element (P1,P2)) representing [[s^i t^j, P1 e1 + P2 e2],[0,1]]
def gmul(x,y):
    (m1,(p1,q1)),(m2,(p2,q2))=x,y
    mono={m1:1}
    return ((m1[0]+m2[0],m1[1]+m2[1]),(padd(p1,pmul(mono,p2)),padd(q1,pmul(mono,q2))))
def ginv(x):
    (m,(p,q))=x; mi=(-m[0],-m[1]); mono={mi:1}
    return (mi,(padd({},pmul(mono,p),-1),padd({},pmul(mono,q),-1)))
GEN={'a':((1,0),({(0,0):1},{})),'b':((0,1),({},{(0,0):1}))}
GEN['A']=ginv(GEN['a']); GEN['B']=ginv(GEN['b'])
def ev(word):
    x=((0,0),({},{}))
    for ch in word: x=gmul(x,GEN[ch])
    return x
def inv(word): return ''.join(ch.swapcase() for ch in reversed(word))
R1='bAABaaBAba'; R2='bAAABaaaBAAbaa'; C='abAB'
prod='aa'+R1+'AA' + 'a'+R1+'A' + 'aa'+inv(R2)+'AA'
print('identity holds mod F2\'\':', ev(C)==ev(prod))
# (2) permutation check; words act with the LAST letter first, as in the landed artifact
def compose_word(word,A,B,n):
    Ai=[0]*n; Bi=[0]*n
    for i in range(n): Ai[A[i]]=i; Bi[B[i]]=i
    M={'a':A,'A':Ai,'b':B,'B':Bi}
    cur=list(range(n))
    for ch in reversed(word):
        P=M[ch]; cur=[P[x] for x in cur]
    return cur
def moved(P): return sum(1 for i,x in enumerate(P) if i!=x)
worst=None; checked=0; viol=0
def test(A,B,n):
    global worst,checked,viol
    mc=moved(compose_word(C,A,B,n))
    if mc==0: return
    m1=moved(compose_word(R1,A,B,n)); m2=moved(compose_word(R2,A,B,n))
    checked+=1
    if mc > 2*m1+m2: viol+=1; print('VIOLATION',n,A,B,m1,m2,mc)
    r=max(m1,m2)/mc; s=(m1+m2)/mc
    if worst is None or r<worst[0]: worst=(r,s,n,m1,m2,mc)
# affine maps on Z/p: x -> alpha x + beta (group AGL(1,p) is metabelian)
for p in [3,5,7,11,13,17,19,23]:
    for a1 in range(1,p):
        for b1 in range(p):
            for a2 in range(1,p):
                for b2 in range(p):
                    test([(a1*x+b1)%p for x in range(p)],[(a2*x+b2)%p for x in range(p)],p)
# lamplighter-type: Z/k-valued lamps on Z/m, points (pos, lamp config) -- metabelian (abelian by abelian)
random.seed(1)
for (k,m) in [(2,3),(2,4),(3,3),(2,5)]:
    pts=[(pos,cfg) for pos in range(m) for cfg in itertools.product(range(k),repeat=m)]
    idx={pt:i for i,pt in enumerate(pts)}; n=len(pts)
    for trial in range(300):
        def mk():
            shift=random.randrange(m); add=[random.randrange(k) for _ in range(m)]; rot=random.randrange(m)
            # (pos,cfg) -> (pos+shift, cfg shifted by rot then plus add)  -- affine on the abelian group Z/m x (Z/k)^m? use semidirect
            def f(pt):
                pos,cfg=pt
                newcfg=tuple((cfg[(i-shift)%m]+add[(i-pos)%m] if False else cfg[(i-shift)%m]+add[i])%k for i in range(m))
                return ((pos+shift)%m,newcfg)
            return [idx[f(pt)] for pt in pts]
        test(mk(),mk(),n)
print('metabelian pairs with t>0 checked:',checked,'violations:',viol,'best (max ratio, sum ratio, n, m1, m2, mc):',worst)
