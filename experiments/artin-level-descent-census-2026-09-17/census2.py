"""Exhaustive-2-dim census of 5-vertex two-block non-star dead cuts.

Usage: python3 census2.py NINST SEED L[,L2..] [NV]
Each instance: random labelled graph on NV vertices (label 'absent' allowed), chi in {+1,-1}
constant on odd classes, filtered to r = 2 blocks, non-star crossing set, block graph
connected, circuit rank >= 3. For every 2-dim rep over F_l (up to conjugation of the first
vertex) with all crossing sigma's singular, compute c0 and ct (enum2).
Instance verdicts:
  NONMEMBER  some rep has ct > 0             ([chi] not in Sigma^1, exact over F_l(t))
  CANDIDATE  some rep has c0 > 0, none ct>0  (L_0 not onto, no twisted witness in dim 2)
  SILENT     no rep has c0 > 0
"""
import itertools
import random
import sys
import time

from census import instance_data, is_star, block_graph_connected, circuit_rank, odd_classes
from enum2 import enumerate_reps, Group


def random_graph(rng, nv):
    V = [chr(ord('a') + i) for i in range(nv)]
    E = {}
    for a, b in itertools.combinations(V, 2):
        if rng.random() < 0.85:
            E[(a, b)] = rng.choice([2, 2, 2, 3, 4, 4, 4, 6, 6, 8, 10])
    cl = odd_classes(V, E)
    vals = {c: rng.choice([1, -1]) for c in set(cl.values())}
    chi = {v: vals[cl[v]] for v in V}
    return V, E, chi


def canon(V, E, chi):
    best = None
    for perm in itertools.permutations(V):
        mp = dict(zip(V, perm))
        for sgn in (1, -1):
            e = tuple(sorted((tuple(sorted((mp[a], mp[b]))), m) for (a, b), m in E.items()))
            c = tuple(sorted((mp[v], sgn * chi[v]) for v in V))
            key = (e, c)
            if best is None or key < best:
                best = key
    return best


def main(ninst, seed, ls, nv):
    rng = random.Random(seed)
    groups = {l: Group(l, 6) for l in ls}
    seen = set()
    count = {"NONMEMBER": 0, "CANDIDATE": 0, "SILENT": 0}
    tries = 0
    n = 0
    while n < ninst and tries < 5000 * ninst:
        tries += 1
        V, E, chi = random_graph(rng, nv)
        comp, blocks, cross = instance_data(V, E, chi)
        if len(blocks) != 2 or not cross or is_star(cross):
            continue
        if not block_graph_connected(blocks, comp, cross) or circuit_rank(V, E) < 3:
            continue
        key = canon(V, E, chi)
        if key in seen:
            continue
        seen.add(key)
        n += 1
        verdict, info = "SILENT", []
        t0 = time.time()
        for l in ls:
            st, ex, _ = enumerate_reps(V, E, chi, l, grp=groups[l])
            info.append((l, st["reps"], st["c0pos"], st["ctpos"]))
            if st["ctpos"] > 0:
                verdict = "NONMEMBER"
                break
            if st["c0pos"] > 0:
                verdict = "CANDIDATE"
        count[verdict] += 1
        print(verdict, "E=", E, "chi=", chi, "cross=", cross, "data(l,reps,c0pos,ctpos)=", info,
              f"{time.time() - t0:.1f}s", flush=True)
    print("SUMMARY seed", seed, "nv", nv, "ls", ls, count, flush=True)


if __name__ == "__main__":
    nv = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    main(int(sys.argv[1]), int(sys.argv[2]), [int(x) for x in sys.argv[3].split(',')], nv)
