import sys,time
from search import Setup
S=Setup('H4',3)
t=time.time()
for L in (1,2):
    print('Y',L,len(S.reps(S.Y,L)),time.time()-t,flush=True)
for L in (1,2):
    print('X',L,len(S.reps(S.X,L)),time.time()-t,flush=True)
