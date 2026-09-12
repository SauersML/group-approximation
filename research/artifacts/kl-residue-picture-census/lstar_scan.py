#!/usr/bin/env python3
"""Measured scan for small KL residue pictures over the binary Leavitt unit group.

Lane kl-curvature-redistribution, 2026-09-12.  For each residue shape that is still
open with involution loops, and for coefficient triples (g, x, y) from short lists
of units of R^x = L_(F_2)(1,2)^x with x, y involutions, it evaluates every face
label of every reduced planar pairing of area two and four (from pairings.c) in
R^x.  A pairing with at most one nontrivial face would be a coefficient-boundary
picture, i.e. a Kervaire--Laudenbach violation over R^x.  Such a hit is only a
candidate: it is re-evaluated with the dual normal-form check and must still be
turned into a certificate for certcheck.py.

Face words are first reduced in U = Z(g) * C_2(x) * C_2(y), which is valid in any
group where x and y are involutions, so words trivial in U are skipped.
"""
import sys
import time

CERT = '/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates'
sys.path.insert(0, CERT)
import leavitt as L  # noqa: E402
from census import SHAPES, NAMES, corner_labels, label, load_faces, reduce_word  # noqa: E402

OPEN = {0: ['111g', '11g1', '1g11', 'g111', '11gg', '1g1g', '1gg1'],
        1: SHAPES[1]}
ORDERS = {'x': 2, 'y': 2}
TIME_LIMIT = float(sys.argv[1]) if len(sys.argv) > 1 else 1500.0


def units():
    std = L.standard_units()
    u, v, w, g3 = std['@u'], std['@v'], std['@w'], std['@g']
    T = L.thompson_unit
    swap = T(['00', '01', '1'], ['01', '00', '1'])
    inv = {'u': u, 'v': v, 'w': w, 'u^g': g3 * u * g3.inverse(),
           'v^g': g3 * v * g3.inverse(), 'swap00-01': swap}
    x0 = T(['0', '10', '11'], ['00', '01', '1'])
    x1 = T(['0', '10', '110', '111'], ['0', '100', '101', '11'])
    rot = T(['0', '10', '11'], ['10', '11', '0'])
    gen = {'g3': g3, 'x0': x0, 'x1': x1, 'uw': u * w, 'vw': v * w, 'rot3': rot}
    for name, a in inv.items():
        assert a.order(4) == 2, name
    for name, a in gen.items():
        assert not a.is_identity(), name
    return inv, gen


def evaluate(word, gens, cache):
    """Product of a word in R^x, extending the longest cached prefix."""
    k = len(word)
    while k > 0 and word[:k] not in cache:
        k -= 1
    value = cache[word[:k]] if k else L.IDENTITY
    for i in range(k, len(word)):
        n, e = word[i]
        value = value * gens[(n, 1 if e > 0 else -1)] ** abs(e)
        cache[word[:i + 1]] = value
    return value


def main():
    start = time.time()
    inv, gen = units()
    shapes = []
    for cls in (0, 1):
        faces = {area: load_faces(cls, area) for area in (2, 4)}
        for shape in OPEN[cls]:
            labels = corner_labels(cls, shape)
            words = {}
            pairings = []
            for area in (2, 4):
                for fs in faces[area]:
                    ids = []
                    for f in fs:
                        wrd = reduce_word(label(f, labels), ORDERS)
                        if wrd:
                            ids.append(words.setdefault(wrd, len(words)))
                    if len(ids) >= 1:
                        pairings.append((area, fs, tuple(ids)))
            shapes.append((cls, shape, pairings, sorted(words, key=words.get)))
            print('shape %s %s: %d pairings, %d distinct nontrivial face words in U'
                  % (NAMES[cls], shape, len(pairings), len(words)))
    sys.stdout.flush()
    triples = [(gname, xname, yname) for gname in gen for xname in inv for yname in inv]
    stats = {(c, s): [0, None, 0] for c, s, _, _ in shapes}   # triples done, min nontrivial, hits
    hits = []
    done = 0
    for gname, xname, yname in triples:
        if time.time() - start > TIME_LIMIT:
            break
        g, x, y = gen[gname], inv[xname], inv[yname]
        gens = {('g', 1): g, ('g', -1): g.inverse(), ('x', 1): x, ('x', -1): x,
                ('y', 1): y, ('y', -1): y}
        cache = {}
        for cls, shape, pairings, wordlist in shapes:
            trivial = [evaluate(wrd, gens, cache).is_identity() for wrd in wordlist]
            st = stats[(cls, shape)]
            st[0] += 1
            for area, fs, ids in pairings:
                k = sum(not trivial[i] for i in ids)
                st[1] = k if st[1] is None else min(st[1], k)
                if k <= 1:
                    st[2] += 1
                    hits.append((cls, shape, gname, xname, yname, area, fs))
        done += 1
        if done % 10 == 0:
            print('progress %d/%d triples, %.0fs, hits so far %d'
                  % (done, len(triples), time.time() - start, len(hits)))
            sys.stdout.flush()
    print('triples covered %d of %d in %.0fs' % (done, len(triples), time.time() - start))
    for (cls, shape), (n, mn, h) in sorted(stats.items()):
        print('  %s %s: triples %d, min nontrivial faces %s, candidate hits %d'
              % (NAMES[cls], shape, n, mn, h))
    if hits:
        L.set_dual(True)
        for cls, shape, gname, xname, yname, area, fs in hits[:20]:
            labels = corner_labels(cls, shape)
            gens = {('g', 1): gen[gname], ('g', -1): gen[gname].inverse(),
                    ('x', 1): inv[xname], ('x', -1): inv[xname],
                    ('y', 1): inv[yname], ('y', -1): inv[yname]}
            k = 0
            for f in fs:
                wrd = reduce_word(label(f, labels), ORDERS)
                if wrd and not evaluate(wrd, gens, {}).is_identity():
                    k += 1
            print('HIT recheck', NAMES[cls], shape, gname, xname, yname, 'area', area,
                  'nontrivial faces', k, 'faces', fs)
    print('KLCR_LSTAR_DONE')


if __name__ == '__main__':
    main()
