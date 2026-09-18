# Configuration-matching test (bh-finf-hyp, 2026-09-18)

- **The run.** One Slurm job, 1328791 (msismall, node acl11, 4 cores, 37 s, 1.2 GB). Output is
  in `/projects/standard/hsiehph/sauer354/bh-finf-hyp/cfg-1328791.out`. The script is
  `cfg_test.py`: the cone-matching script of `gq-bh-finf-hyp-cone-matching-test.md` plus the
  block below.
- **What it computes.** For every atom `D` that fails cone matching under a generator `k`, it
  finds the smallest union `U ∋ D` of level-`n` atoms for which `kU` is, exactly on the window,
  a union of level-`m` atoms (`m ∈ [n−2, n+2]`). It reports `U<|U|> -> C<#image atoms>`.

## Results (every generator gives the same numbers)

| group | levels | bad atoms per level | configuration of each bad atom |
|---|---|---|---|
| free3 (tree) | 1–5 | 1 at level 1, then 0 | `U1 -> C2` (the root direction) |
| square (Z² grid) | 1–9 | 4 | `U1 -> C2` at every level |
| pentagon (R0 = 8, N = 6) | 1–5 | 5, then 4 | `U1 -> C2` at every level (one `U1 -> C3` at level 1) |
| hexagon (R0 = 7, N = 4) | 1–3 | 5, 6, 6 | `U1 -> C2` (4 per level) and `U1 -> C3` (2 per level) |

**Reading.**
- **No partners are needed.** Every bad atom maps exactly onto a union of 2 or 3 atoms at a
  single level. That number is bounded, independent of the level, and the same for every
  generator.
- **The grid shows the same pattern.** So this test does not separate the control from the
  hyperbolic groups. Bounded configuration images are necessary for a configuration-tile engine,
  but not sufficient.

## Added code (inside the per-level loop of `analyse`)

```python
            # Configuration closure: the smallest union U of level-n atoms containing a bad atom D
            # such that kU is (window-exactly) a union of level-m atoms; report (|U|, #image atoms).
            bads = [D for D in classes if nonmatch[(n, D)]]
            best = {D: None for D in bads}
            for m in range(max(1, n - 2), min(N, n + 2) + 1):
                szm = size[m]
                T = {}
                for w in W1:
                    T.setdefault(fullkey[w][:szm], set()).add(fullkey[img[w]][:szn])
                Cimg = {E: {fullkey[img[i]][:szm] for i in X} for E, X in classes.items()}
                for D in bads:
                    U = {D}
                    ok = True
                    while True:
                        CU = set()
                        for E in U:
                            if E not in Cimg:
                                ok = False
                                break
                            CU |= Cimg[E]
                        if not ok:
                            break
                        newU = set(U)
                        for C in CU:
                            newU |= T.get(C, set())
                        if newU == U:
                            break
                        U = newU
                        if len(U) > 12:
                            ok = False
                            break
                    if not ok:
                        continue
                    cand = (len(U), len(CU), m, sum(1 for E in U if nonmatch.get((n, E), False)))
                    if best[D] is None or cand[:2] < best[D][:2]:
                        best[D] = cand
            hist = {}
            for D, b in best.items():
                key = 'none' if b is None else f"U{b[0]}->C{b[1]}(bad{b[3]})"
                hist[key] = hist.get(key, 0) + 1
            row['config'] = hist
```
