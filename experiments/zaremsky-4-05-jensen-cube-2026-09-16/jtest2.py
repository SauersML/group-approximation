import sys, random
from raagcube import RAAG
from jtest import run
rng = random.Random(int(sys.argv[1]))
R = int(sys.argv[2]); trials = int(sys.argv[3]); ms = int(sys.argv[4])
graphs = {
 'P4': RAAG(4, [(0,1),(1,2),(2,3)]),
 'K1*P4': RAAG(5, [(0,1),(1,2),(2,3),(4,0),(4,1),(4,2),(4,3)]),
 'C5': RAAG(5, [(0,1),(1,2),(2,3),(3,4),(4,0)]),
 'K4-minus-path': RAAG(4, [(0,1),(0,2),(1,2),(2,3)]),
}
for nm in sys.argv[5].split(','):
    run(graphs[nm], nm, R, trials, ms, rng)
