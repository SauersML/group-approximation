from engine import *
from math import sqrt
def pstar(m,v=2):
    d=4*m+v; la=v+2*sqrt(3)*m; return 2/(la+sqrt(la*la-4*(d-1)))
for J in [1,2,3]:
  for V in [0,1]:
    FM=first_moment_terms(J,bool(V))
    up=[t for t in FM if t[1]>0]
    row=[]
    for m in [3,4,5,6,8,10,12,14,17]:
        ps=pstar(m)
        row.append((m, round(3*float(wblock(up,m,F(ps))),4), round(3*float(wblock(FM,m,F(ps))),4)))
    print('J',J,'V',V,row)
