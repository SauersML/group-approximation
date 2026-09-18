# Is c1 = b1 b0^-1 in H = phi_2(St_B(2)) exactly?  DFS over words in {b0,b0^-1,c1,c2,c3}, prepending letters.
import sys, itertools as it, numpy as np
from agrp import AG
# B on alphabet {0,1,2}: states b0,b1,b2 (0,1,2) and inverses 3,4,5; add c1,c2,c3 as states 6,7,8 (involutions)
O=[(1,2,0),(1,0,2),(1,0,2),(2,1,0),(2,1,0),(0,1,2)]
S=[(1,1,1),(0,2,2),(2,0,0)]
G0=AG(O[:3],S)
# c1=(02)(c3,c1,c3), c2=(02)(c1,c3,c1), c3=(c2,c2,c2)
Cg=AG([(2,1,0),(2,1,0),(0,1,2)],[(2,0,2),(0,2,0),(1,1,1)])
N=int(sys.argv[2]) if len(sys.argv)>2 else 5
L=int(sys.argv[1])
W=list(it.product(range(3),repeat=N)); idx={w:i for i,w in enumerate(W)}
def perm(G,w): return np.array([idx[G.act_path(w,x)[0]] for x in W])
# letters: 0 b0, 1 b0^-1, 2 c1, 3 c2, 4 c3 ; out and sections (as letters of an extended alphabet of section perms)
P={}
for g in range(6): P[('b',g)]=perm(G0,(g,))
for g in range(3): P[('c',g)]=perm(Cg,(g,))
# letter -> (out perm, section keys per input x)
b0inv_sec=[('b',4)]*3
LET={0:((1,2,0),[('b',1)]*3), 1:((2,0,1),b0inv_sec), 2:((2,1,0),[('c',2),('c',0),('c',2)]),
     3:((2,1,0),[('c',0),('c',2),('c',0)]), 4:((0,1,2),[('c',1)]*3)}
names=['b0','B0','c1','c2','c3']
tc1=P[('c',0)]; tb1=P[('b',1)]
ident=np.arange(len(W))
found=[]
def dfs(word,y,s,depth):
    if y==2 and len(word)>0:
        for tgt,nm in ((tc1,'c1'),(tb1,'b1')):
            if np.array_equal(s,tgt): found.append((nm,list(word))); print('HIT',nm,' '.join(names[a] for a in word),flush=True)
    if depth==L: return
    last=word[0] if word else None
    for a in range(5):
        if last is not None:
            if (a,last) in ((0,1),(1,0)) or (a>=2 and last>=2): continue   # reduced; c's collapse
        out,sec=LET[a]
        s2=P[sec[y]][s]            # s first, then a|_y
        dfs([a]+word,out[y],s2,depth+1)
dfs([],2,ident,0)
print('done L',L,'hits',len(found))
