import sys, math
from gmin import run
k=int(sys.argv[1]); ws=[int(v) for v in sys.argv[2].split(',')]; rest=int(sys.argv[3])
for w in ws:
    E=[(i,j) for i in range(w) for j in range(i+1,w) if j-i<=k]
    c=run(w,E,rest=rest)
    print("k",k,"w",w,"edges",len(E),"free",len(E)-w+1,"c %.5f c/w %.5f c/(sqrt3 w) %.5f"%(c,c/w,c/w/math.sqrt(3)),flush=True)
