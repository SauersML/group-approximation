# localsum.py in.jsonl : for every candidate record (both automaton images not certified finite), the local
# actions (order, transitive) of <A> on the vertical letters and of <B> on the horizontal letters, the
# Thompson-Wielandt irreducibility test at radius 2 (irred_tw.certify, sides V and H), and which certificate
# closed the class (R4 tree, R6s4 tree, R6s4 cone lemmas, or none).
import sys, json
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import VH
from vh_enum import inv_arr
from irred_tw import certify
from sympy.combinatorics import Permutation, PermutationGroup
for l in open(sys.argv[1]):
    r = json.loads(l)
    if not r.get('cand'): continue
    m, pA, n, pB = int(r['pat'][0]), int(r['pat'][1]), int(r['pat'][3]), int(r['pat'][4])
    G = VH(inv_arr(m, pA), inv_arr(n, pB), {tuple(a): tuple(b) for a, b in r['sq']}); G.confluence()
    PV = PermutationGroup([Permutation([G.SQ[(h, v)][0] for v in range(n)]) for h in range(m)])
    tw = {s: certify(G, 2, s)['irreducible'] for s in 'VH'}
    how = 'R4' if r.get('tree4') else 'R6s4' if r.get('tree6s4') else \
          'cone' if (r.get('cone6s4') or {}).get('cert') else 'none'
    loc = certify(G, 1, 'H')
    print(json.dumps(dict(pat=r['pat'], seed=r['seed'], klein=r['klein'], locV=[int(PV.order()), PV.is_transitive()],
                          locH=loc['local_order'], tw=tw, cert=how)), flush=True)
