# wcheck.py WINDOW WEIGHTS RUNS: RUNS independent single-start minimisations of c(G[W], w) (wdens.cw);
# prints the best values and the needed values 12 sqrt3 |w|/14 (n = 14) and 11 sqrt3 |w|/13 (n = 13).
import sys, numpy as np
from fractions import Fraction as Fr
from wdens import cw
WIN=[int(v) for v in sys.argv[1].split(',')]; w=[float(Fr(v)) for v in sys.argv[2].split(',')]; R=int(sys.argv[3])
vals=sorted(cw(WIN,w,1,seed=s)[0] for s in range(R)); S=sum(w)
print("W",WIN,"w",sys.argv[2],"|w| %.6f"%S,"best c<= %.6f"%vals[0],"next",np.round(vals[1:6],5).tolist())
for n,R_ in ((14,12),(13,11)):
    need=np.sqrt(3)*R_*S/n; print("n=%d needs c >= %.6f   margin %.3f%%"%(n,need,100*(vals[0]/need-1)))
