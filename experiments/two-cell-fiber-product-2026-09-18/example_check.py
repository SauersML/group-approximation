# Exact check of the explicit ratio-2 configuration (claim two-cell-w-cycle-pairs-of-ratio-two-exist).
# G = <x,y | w>, w = x y^4 x^-1 y^-1 x y^2 x^-1 y^-5; Gamma: vertices 0,1,2; edges below (letter 0=x,1=y).
import sympy as sp
import census as C
from finchar import finchar, bprime
edges=[(0,0,0),(1,2,0),(0,1,1),(1,0,1),(2,2,1)]
w=[C.LET.index(ch) for ch in "xyyyyXYxyyXYYYYY"]
tr=C.mk(edges); C.NE=len(edges)
r0=C.read(tr,0,w); r1=C.read(tr,1,w)
print("closed:",r0[0]==0,r1[0]==1," z0 =",r0[1]," z1 =",r1[1])
c=C.crow(3,edges,tr,0,1,w)
print("c =",[sp.factor(ci) for ci in c])
s,t=C.s,C.t
print("c at (s,t)=(-1,2):",[ci.subs({s:-1,t:2}) for ci in c])
print("c at sign character (s,t)=(-1,-1):",[ci.subs({s:-1,t:-1}) for ci in c])
print("finite-character certificate:",finchar(edges,tr,0,1,w)," B' abelian shadow holds:",bprime(edges,tr,0,1))
