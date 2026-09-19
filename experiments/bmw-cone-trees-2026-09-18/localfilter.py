# Local-action filter for a quaternionic (arithmetic PGL_2) model: for each remaining class, the local
# action groups on both trees (orders), and whether they are compatible with PSL_2(F_q) <= L <= PGL_2(F_q)
# acting on P^1(F_q), q + 1 = valency.
import sys, json
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import load
from localact import local
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
REM = json.load(open(sys.argv[1]))
OK = {3: {6}, 4: {12, 24}, 5: {60}}      # |PSL_2(F_q)| .. |PGL_2(F_q)| with 2-transitivity
out = {}
for pat, rem in REM.items():
    rem = set(rem)
    for i, G in load(C + 'census_%s.json' % pat):
        if i not in rem: continue
        lv, lh = local(G, 'V'), local(G, 'H')
        # side V: <A> acting on the n vertical letters (valency n); side H: <B> on the m horizontal letters
        okv = lv['order'] in OK[G.n] and lv['two_transitive']; okh = lh['order'] in OK[G.m] and lh['two_transitive']
        out['%s#%d' % (pat, i)] = dict(V=lv['order'], V2tr=lv['two_transitive'], H=lh['order'], H2tr=lh['two_transitive'], pass_=okv and okh)
    print(pat, len(rem), 'pass', [k for k, v in out.items() if k.startswith(pat) and v['pass_']], flush=True)
json.dump(out, open(sys.argv[2], 'w'), indent=0)
