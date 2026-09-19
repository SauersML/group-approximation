# Run the C++ cone-tree finder ctree (compile: g++ -O2 -o ctree ctree.cpp) on one census class.
# usage: ctree.py census_<pattern>.json class R SHORT MAXLEAVES TIMEOUT_S  -> prints the tree JSON line
import sys, json, subprocess, os
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
f, ci = sys.argv[1], int(sys.argv[2])
D = json.load(open(C + f)); rep = D['reps'][ci]
txt = '%d %d\n%s\n%s\n' % (len(D['iA']), len(D['iB']), ' '.join(map(str, D['iA'])), ' '.join(map(str, D['iB'])))
txt += ''.join('%d %d %d %d\n' % (a[0], a[1], b[0], b[1]) for a, b in rep)
here = os.path.dirname(os.path.abspath(__file__))
p = subprocess.run([os.path.join(here, 'ctree')] + sys.argv[3:7] + [str(ci)], input=txt, capture_output=True, text=True)
sys.stderr.write(p.stderr); sys.stdout.write(p.stdout)
sys.exit(p.returncode)
