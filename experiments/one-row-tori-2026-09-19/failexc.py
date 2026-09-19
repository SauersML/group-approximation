# least excision m<=M for listed (n th al be ga), direct conjugacy test (see fails.py)
import sys
from fails_lib import exm
from lib import arcx
M=int(sys.argv[1])
for line in sys.stdin:
    n,th,al,be,ga=map(int,line.split()[:5]); print(line.strip(),'exc',exm(arcx(n,th,al,be,ga).tolist(),M),flush=True)
