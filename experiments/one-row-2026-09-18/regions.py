import numpy as np
from prof import *
n,th,al,be,ga=400,157,229,75,96
c=arcx(n,th,al,be,ga); x=np.arange(n)
def cp(q):
    y=x.copy()
    for _ in range(q): y=c[y]
    return y
F1=(cp(3)-x)%n==(-4)%n; F2=(cp(2)-x)%n==10
def arcs(F):
    idx=np.flatnonzero(F); 
    if len(idx)==0: return []
    runs=[]; s=idx[0]; prev=idx[0]
    for i in idx[1:]:
        if i!=prev+1: runs.append((s,prev)); s=i
        prev=i
    runs.append((s,prev)); return runs
print('F1',F1.sum(),arcs(F1)); print('F2',F2.sum(),arcs(F2))
print('both',(F1&F2).sum(),'neither',(~F1&~F2).sum(), arcs(~F1&~F2))
print('breaks', [0,al,al+be], 'images', [th,(th+al)%n,(th+al+ga)%n])
