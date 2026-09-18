#!/usr/bin/env python3
"""Sharded single-length census of two-generator one-relator relators against the landed
certifier (hierarchy rules + rule 1 + rule R) and, with --amalgam, rule N of
nilpotent_root_certify.py followed by its Nielsen-image search for the words still open.

Usage:  census_shard.py L K i [--amalgam]
  L  relator length;  K shards;  i in 0..K-1 this shard.
Only cyclically reduced words w of length L whose canonical form (hierarchy_certify.canon)
is w itself (letters a=0, b=1) are processed, so every cyclic/inversion/relabelling class
is visited exactly once over all shards.  A class goes to shard the index of its length-6 prefix mod K.  Output: counts per (landed, +R, +A) and the list of
relators no rule certifies.
"""
import os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "perfect-kernel-segment-targets-2026-09-17"))
import retract_segment_certify as rsc  # noqa: E402  (patches hc.root_tower_ok: landed + rule 1 + rule R)
hc = rsc.hc

USE_A = "--amalgam" in sys.argv
if USE_A:
    import nilpotent_root_certify as asc  # noqa: E402  (adds rule N on top)


def code(k):
    c = 0
    for a, e in k:
        c = 4 * c + 2 * a + (e > 0)
    return c


def words(L, K, i, P=6):
    """Cyclically reduced words of length L starting with a^-1 (canonical forms start
    with (0,-1)) whose length-P prefix has index = i mod K (prefixes numbered in
    enumeration order), so the shards partition the words."""
    gens = [(0, 1), (0, -1), (1, 1), (1, -1)]
    w = [(0, -1)]

    cnt = [0]

    def rec():
        if len(w) == P:
            cnt[0] += 1
            if (cnt[0] - 1) % K != i:
                return
        if len(w) == L:
            if not (w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]):
                yield tuple(w)
            return
        for g in gens:
            if w[-1][0] == g[0] and w[-1][1] == -g[1]:
                continue
            w.append(g)
            yield from rec()
            w.pop()
    yield from rec()


def main():
    L, K, i = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    t0 = time.time()
    stats, opens = {}, []
    memo_old, memo_R, memo_A = {}, {}, {}
    for w in words(L, K, i):
        if len({a for a, _ in w}) < 2:
            continue
        k = hc.canon(w)
        if k != w:
            continue
        if hc.is_proper_power(k):
            continue
        rsc.MODE["R"] = False
        if USE_A:
            asc.MODE["A"] = False
        a, _ = hc.certify(k, "new", memo=memo_old)
        b, c, why = a, a, ""
        d = None
        if not a:
            rsc.WHY.clear()
            if USE_A:
                asc.WHY.clear()
            rsc.MODE["R"] = True
            b, why = hc.certify(k, "new", memo=memo_R)
            c = b
            if not b and USE_A:
                asc.MODE["A"] = True
                c, why = hc.certify(k, "new", memo=memo_A)
                if not c:
                    c, why = asc.nielsen_search(k)
                    d = c
                asc.MODE["A"] = False
            rsc.MODE["R"] = False
        key = (a, b, c) if d is None else (a, b, "nielsen" if d else False)
        stats[key] = stats.get(key, 0) + 1
        if not c:
            opens.append((k, why))
        elif not a:
            rules = sorted(set(rsc.WHY.values()) | (set(asc.WHY.values()) if USE_A else set()))
            opens.append((k, "CERT " + (why if why else "") + " " + ";".join(rules)))
    print("# L=%d shard %d/%d amalgam=%s time %.1fs" % (L, i, K, USE_A, time.time() - t0))
    print("landed+rule1  +ruleR  +ruleN(+nielsen-search)  count")
    for key in sorted(stats, key=str):
        print(*key, stats[key])
    print("needs-new-rule-or-open:")
    for k, why in opens:
        print(L, "".join(("ab"[a] if e == 1 else "AB"[a]) for a, e in k), why)
    print("EXIT 0")


if __name__ == "__main__":
    main()
