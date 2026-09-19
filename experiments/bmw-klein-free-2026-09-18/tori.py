import sys, json
from collections import deque
C='/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
f, ci, QM, SW = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), '--swap' in sys.argv
D=json.load(open(C+f)); m,n,iA,iB=D['m'],D['n'],D['iA'],D['iB']
SQ={tuple(a):tuple(b) for a,b in D['reps'][ci]}
VH={}
for (h,v),(v2,h2) in SQ.items(): VH[(iB[v2],h)]=(h2,iB[v])
if SW: T,nb,ilB,na,ilA=SQ,m,iA,n,iB
else: T,nb,ilB,na,ilA=VH,n,iB,m,iA
def push(s,c):
    s=list(s)
    for i in range(len(s)-1,-1,-1): c,s[i]=T[(s[i],c)]
    return c,tuple(s)
def winv(w,il): return tuple(il[c] for c in reversed(w))
def S(w): return ''.join(map(str,w))
for q in range(2,QM+1,2):
    W=[()]
    for _ in range(q): W=[w+(c,) for w in W for c in range(nb) if not w or w[-1]!=ilB[c]]
    adj={w:[] for w in W}
    for s in W:
        for c in range(na):
            c2,s2=push(s,c)
            if c2==c: adj[s].append((c,s2))
    # BFS in reduced-label space from each B: states (s,lastletter); find shortest reduced A to B (commute) and to B^-1
    res=[]
    for B in W:
        if B[0]==ilB[B[-1]]: continue  # cyclically reduced only
        Bi=winv(B,ilB)
        seen={(B,-1):()}; dq=deque([(B,-1)]); com=inv=None
        while dq and (com is None or inv is None):
            s,l=dq.popleft(); A=seen[(s,l)]
            if len(A)>40: break
            for c,s2 in adj[s]:
                if l>=0 and c==ilA[l]: continue
                if (s2,c) in seen: continue
                A2=A+(c,); seen[(s2,c)]=A2; dq.append((s2,c))
                if s2==B and com is None: com=A2
                if s2==Bi and inv is None: inv=A2
        if com or inv: res.append((S(B),S(com) if com else None,S(inv) if inv else None))
    print(q,len(res),res[:12],flush=True)
