#!/usr/bin/env python3
# bh-free-61: complement closure for the edge-split operad O_E at m = 2.
# S = set of O_E-dissections of Delta (modulo S_3), containing the atoms. S is CLOSED if for all A, B in S
# (B in any S_3 position relative to A) there is a common >=_E upper bound U whose restrictions U|l to
# every leaf l of A and of B (in l's frame) lie in S or are trivial. A finite closed S gives Ore's
# condition by the Garside grid: two S-forests are completed square by square, each square staying in S.
# This script builds S greedily: for each pair it picks, among the common upper bounds of the two smallest
# available sizes, one that adds the fewest new elements. It stops when a pass adds nothing (closed) or
# when a pair has no common upper bound within the window (then closure is unverified).
import sys, json, time
import spine as sp

def restrict(U, l):
    pieces = [P for P in U if sp.cell_in(l, P)]
    D = sp.in_frame(l, pieces)
    return None if len(D) == 1 else sp.canon(D)

def cubs_two_levels(A, B, N):
    P, Q = (A, B) if len(A) >= len(B) else (B, A)
    found, first = [], None
    try:
        for lev in sp.refinements(P, N):
            k = len(next(iter(lev)))
            if first is not None and k > first + 1: break
            for U in lev:
                if sp.refines_E(U, Q):
                    found.append(U)
                    if first is None: first = k
    except OverflowError:
        pass
    return found

def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    maxpass = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    t0 = time.time()
    S = {sp.canon(a): a for a in sp.atoms()}      # canonical form -> representative dissection
    log = {"N": N, "passes": []}
    done_pairs = {}
    for ps in range(1, maxpass + 1):
        added, trunc, npairs = {}, [], 0
        items = list(S.items())
        for ca, A in items:
            for cb, B0 in items:
                if cb < ca: continue
                for p in sp.PERMS:
                    B = sp.act(B0, p)
                    key = (ca, tuple(sorted(B)))
                    if key in done_pairs: continue
                    npairs += 1
                    cand = cubs_two_levels(A, B, N)
                    if not cand:
                        trunc.append([len(A), len(B)]); continue
                    best = None
                    for U in cand:
                        newset = set()
                        for l in list(A) + list(B):
                            r = restrict(U, l)
                            if r is not None and r not in S and r not in added: newset.add(r)
                        score = (len(newset), len(U))
                        if best is None or score < best[0]: best = (score, U, newset)
                    done_pairs[key] = len(best[1])
                    for r in best[2]:
                        added[r] = frozenset(tuple(map(tuple, c)) for c in r)
        for r, D in added.items(): S[r] = D
        hist = {}
        for r in added: hist[len(r)] = hist.get(len(r), 0) + 1
        rec = {"pass": ps, "pairs": npairs, "added": len(added), "added_by_size": dict(sorted(hist.items())),
               "S_size": len(S), "max_element_size": max(len(k) for k in S), "pairs_without_cub": len(trunc),
               "secs": round(time.time() - t0, 1)}
        log["passes"].append(rec); print(json.dumps(rec), flush=True)
        if trunc: print(json.dumps({"truncated_examples": trunc[:5]}), flush=True)
        if not added and not trunc:
            print(json.dumps({"CLOSED": True, "S_size": len(S), "sizes": sorted(len(k) for k in S)}), flush=True)
            break
    log["S"] = [[list(map(list, c)) for c in k] for k in S]
    log["pair_cub_sizes"] = sorted(done_pairs.values())
    with open("closure.%d.json" % N, "w") as f: json.dump(log, f)

if __name__ == "__main__":
    main()
