# Referee independent check (2026-09-16): Basilica generators as explicit permutations of
# the 2^12 level-12 vertices, right action v^(gh) = (v^g)^h. Independent of the section-word
# recursion in basilica_checks.py; a level-12 check is evidence only, not a proof.
# independent check: permutations of level-n vertices, right action v^(gh)=(v^g)^h
import sys
from functools import lru_cache
N=12
@lru_cache(None)
def gen(name,n):
    # returns tuple perm of range(2^n); vertex = int with first letter as most significant bit
    if n==0: return (0,)
    size=1<<n; half=size>>1
    p=[0]*size
    if name in('a','A'):
        sub=gen('b' if name=='a' else 'B',n-1)
        for v in range(half): p[v]=v; p[half+v]=half+sub[v]
    else:
        if name=='b':
            sub=gen('a',n-1)
            # (1,a)eps : 0v->1v, 1v->0 v^a
            for v in range(half): p[v]=half+v; p[half+v]=sub[v]
        else: # b^-1 = (a^-1,1)eps : 0v -> 1 v^{a^-1}, 1v -> 0v
            sub=gen('A',n-1)
            for v in range(half): p[v]=half+sub[v]; p[half+v]=v
    return tuple(p)
def ev(word,n=N):
    p=list(range(1<<n))
    for x in word:
        g=gen(x,n); p=[g[q] for q in p]   # v^(p x) = (v^p)^x
    return tuple(p)
def inv(w): return ''.join({'a':'A','A':'a','b':'B','B':'b'}[x] for x in reversed(w))
def comm(x,y): return inv(x)+inv(y)+x+y
def conj(x,y): return inv(y)+x+y
idp=tuple(range(1<<N))
print('b inverse ok', ev('bB')==idp and ev('Bb')==idp, ev('aA')==idp)
print('[[b,a],a]=1:', ev(comm(comm('b','a'),'a'))==idp)
print('[a,a^b]=1:', ev(comm('a',conj('a','b')))==idp)
print('[a,a^(b^2)]=1 (should be False):', ev(comm('a',conj('a','bb')))==idp)
sig={'a':'bb','A':'BB','b':'a','B':'A'}
r=comm('a',conj('a','b'))
for k in range(5):
    print('sigma^%d rel'%k, ev(r)==idp); r=''.join(sig[x] for x in r)
# a^t^2 = a^2 in HNN is sigma^2(a)=a^2
print('sigma^2(a)=aa', ''.join(sig[x] for x in ''.join(sig[x] for x in 'a')))
# a^b = (b^a,1): check sections at level N
p=ev(conj('a','b')); q=ev(conj('b','a'),N-1); half=1<<(N-1)
print('a^b=(b^a,1):', all(p[v]==q[v] for v in range(half)) and all(p[half+v]==half+v for v in range(half)))
# sigma(g) = (a^{eps_a g}, g) random
import random; random.seed(1); ok=True
for _ in range(50):
    g=''.join(random.choice('aAbB') for _ in range(random.randint(0,10)))
    e=g.count('a')-g.count('A')
    p=ev(''.join(sig[x] for x in g)); s0=ev(('a' if e>=0 else 'A')*abs(e),N-1); s1=ev(g,N-1)
    ok&= all(p[v]==s0[v] for v in range(half)) and all(p[half+v]==half+s1[v] for v in range(half))
print('sigma formula:',ok)
