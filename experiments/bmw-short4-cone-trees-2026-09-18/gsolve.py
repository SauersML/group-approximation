# Solve a DIMACS CNF with Glucose 4 (pysat) and write its DRUP proof (Glucose emits RUP lemmas only).
# usage: gsolve.py in.cnf out.drat   -> prints SAT/UNSAT and the number of proof lines
import sys
from pysat.formula import CNF
from pysat.solvers import Glucose4
F = CNF(from_file=sys.argv[1])
s = Glucose4(bootstrap_with=F.clauses, with_proof=True)
r = s.solve()
if r: print('SAT'); sys.exit(1)
P = s.get_proof()
open(sys.argv[2], 'w').write('\n'.join(P) + '\n')
print('UNSAT', len(P))
