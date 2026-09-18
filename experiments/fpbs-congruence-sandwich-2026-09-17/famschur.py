import sys,time
from schur3 import build_geometry, certify
L=int(sys.argv[1]); mode=sys.argv[2]
if mode=='rig': D={1:[0,1,3],2:[0,1,4]}
elif mode=='tri': D={1:[0,1,1000],2:[0,1,100000]}
elif mode=='gen': D={1:[0,1000,10**5],2:[0,10**7,10**9]}
t=time.time(); geo=build_geometry(L,D); print(mode,'L',L,'windows',geo[1],time.time()-t,flush=True)
v=None
for p in map(float,sys.argv[3:]):
    C,v=certify(*geo,p,v0=v); print(mode,'L',L,'p',p,'C',C,time.time()-t,flush=True)
