# Local actions of the irreducible candidates (classes not certified reducible) of the given patterns:
# the permutation group of <A> on the vertical letters (side V) and of <B> on the horizontal letters (side H),
# i.e. the local action at a vertex of the closure of each projection.  Tallies the pairs of local-action
# types (order, transitive, primitive, 2-transitive) and lists the classes that are locally 2-transitive on
# both sides together with their Thompson-Wielandt test at radius r (irred_tw.certify) and whether each
# vertex stabilizer is transitive on the spheres of radius 2, 3, 4.
# usage: localact.py r pattern...        e.g. localact.py 3 40_40 41_40
import sys, json, collections
from sympy.combinatorics import Permutation, PermutationGroup
from lo_census import load
from irred_tw import maps, certify, ball_words, act

def sphere_transitive(G, side, r):
    # is the image of the vertex stabilizer transitive on the sphere S(x, r)?  (necessary for local
    # infinite transitivity, i.e. for the projection closure to be 2-transitive on the boundary)
    L, n, inv, step = maps(G, side)
    S = [w for w in ball_words(n, inv, r) if len(w) == r]; ix = {w: i for i, w in enumerate(S)}
    P = PermutationGroup([Permutation([ix[act(step, a, w)] for w in S]) for a in range(L)])
    return bool(P.is_transitive())

def local(G, side):
    L, n, inv, step = maps(G, side)
    gens = [Permutation([step(a, x)[0] for x in range(n)]) for a in range(L)]
    P = PermutationGroup(gens)
    tr = P.is_transitive()
    two = tr and n >= 2 and PermutationGroup(P.stabilizer(0).generators).orbit(1) == set(range(1, n)) if tr else False
    return dict(order=int(P.order()), transitive=bool(tr), primitive=bool(tr and P.is_primitive()), two_transitive=bool(two))

if __name__ == "__main__":
    r = int(sys.argv[1])
    for pat in sys.argv[2:]:
        recs = {json.loads(l)['idx']: json.loads(l) for l in open(f'out_{pat}.jsonl')}
        tally = collections.Counter(); both = []
        for i, G in load(f'census_{pat}.json'):
            rec = recs[i]
            if rec['finH'] is not None and rec['finV'] is not None: continue
            lv, lh = local(G, 'V'), local(G, 'H')
            key = lambda d: f"{d['order']}{'/2tr' if d['two_transitive'] else '/prim' if d['primitive'] else '/tr' if d['transitive'] else ''}"
            tally[(key(lv), key(lh))] += 1
            if lv['two_transitive'] and lh['two_transitive']:
                tv, th = certify(G, r, 'V'), certify(G, r, 'H')
                both.append(dict(idx=i, V=lv['order'], H=lh['order'], tw_V=tv['irreducible'], tw_H=th['irreducible'],
                                 sph_V=[sphere_transitive(G, 'V', k) for k in (2, 3, 4)],
                                 sph_H=[sphere_transitive(G, 'H', k) for k in (2, 3, 4)]))
        print(json.dumps(dict(pattern=pat, candidates=sum(tally.values()),
                              local_types={f'{a} | {b}': c for (a, b), c in sorted(tally.items())},
                              both_2transitive=len(both), both_2tr_tw_certified=sum(b['tw_V'] or b['tw_H'] for b in both),
                              tw_and_spheres_1to4_transitive=sum((b['tw_V'] or b['tw_H']) and all(b['sph_V'] + b['sph_H']) for b in both),
                              both_2tr=both)), flush=True)
