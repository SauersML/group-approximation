---
rg: 2
id: titz-witzel-gate-small-models-defect-mark-ratio-four-thirds
kind: claim
title: On at most eleven points the two-generator Titz--Witzel gate has defect at least four thirds of its mark, attained by S_3
distinct_from:
  titz-witzel-sofic-gate-two-generators-four-approximate-relators: that is the exact reduction of soficity to the marked two-permutation gate (TW2G2)-(TW2G4); this is a finite exhaustive census of that gate on small point sets together with a local-search census on larger ones.
  titz-witzel-kernel-sofic: that is the open asymptotic soficity assertion; this computes the optimal defect-to-mark ratio only for n <= 11 and does not decide it.
  titz-witzel-two-generator-gate-forces-macroscopic-noncommutation: that is a metric inequality valid on every model; this is a computed sharp constant for models of bounded size.
artifacts:
  - experiments/titz-witzel-gate-census-2026-09-17/words.py
  - experiments/titz-witzel-gate-census-2026-09-17/relators.h
  - experiments/titz-witzel-gate-census-2026-09-17/gate_exhaust.c
  - experiments/titz-witzel-gate-census-2026-09-17/exhaust.sh
  - experiments/titz-witzel-gate-census-2026-09-17/exhaust_results.txt
  - experiments/titz-witzel-gate-census-2026-09-17/gate_anneal.c
  - experiments/titz-witzel-gate-census-2026-09-17/sweep.sh
  - experiments/titz-witzel-gate-census-2026-09-17/anneal_results.txt
---

**COMPUTATION (finite, exhaustive), no asymptotic consequence.**

Setting.  Use the words `(TW2G1)` and the four approximate relators
`r_0 = c^2`, `r_1 = rho^2 e^(-1) u^(-1)`, `r_2 = b x u^(-1) d^(-1)`, `r_3 = a c d b`
of `(TW2G2)`, from `titz-witzel-sofic-gate-two-generators-four-approximate-relators`.
Their free-reduced lengths are 18, 84, 108 and 104. For an involution `e` and a
permutation `u` of an `n`-set, put

```text
D(e,u) = sum_{i=0..3} |supp r_i(e,u)|,        M(e,u) = |supp u^8|.
```

`(TW2G4)` asks for models with `D/n -> 0` and `M/n` bounded below. Since the gate
group's only finite quotient is `Z/2`, `D = 0` forces `M = 0`.

**Result.**  For every `n <= 11`, every involution `e` and every `u` in `Sym(n)` with
`M(e,u) > 0` satisfy

```text
D(e,u) >= (4/3) M(e,u).                                   (TWS1)
```

The constant is sharp at every `n >= 3`. Equality holds for the three-point *S_3 gadget*
`e = (0 1)`, `u = (0 2 1)`, i.e. `u(0)=2, u(1)=0, u(2)=1`. There `M = 3`, `r_0` and `r_2`
hold exactly, and `r_1` and `r_3` each move exactly 2 of the 3 points, so `D = 4`.
Disjoint unions of this gadget with fixed points, or with exact mark-zero models, give
`D/M = 4/3` on every `n`. Consequently the minimal normalised defect subject to
`M >= n/4` is at least `1/3` for all `n <= 11`.

**Method (exhaustive part).**  Simultaneous conjugation preserves `D` and `M`, and every
involution of an `n`-set is conjugate to `(0 1)(2 3)...(2k-2 2k-1)` for one
`k <= n/2`. So `gate_exhaust.c` fixes that `e` for each `k` and runs `u` over all of
`Sym(n)` by Heap's algorithm. Words act on the right, as a homomorphism from the free group
with generators inverted. This is again a model of the gate, and `u <-> u^(-1)` is a
bijection on `Sym(n)`, so the enumerated set of `(D, M)` values is exactly that of the
genuine assignments. The relators are generated literally from
`research/artifacts/titz-witzel-two-generator-free-word-check.py` by `words.py`, which
prints the lengths 18, 84, 108, 104. A pair is abandoned early only once its partial
defect exceeds every running minimum, so the reported minima are exact.
Output is `exhaust_results.txt`, one line per `(n,k)`, `3 <= n <= 11`, each followed by
witness pairs.

| n | u with M>0 (per k) | min D over M>0 | min D/M | min D with 4M >= n |
|---|---|---|---|---|
| 3 | 2 | 4 | 4/3 | 4 |
| 8 | 29056 | 4 | 4/3 | 4 |
| 9 | 283904 | 4 | 4/3 | 4 |
| 10 | 2956544 | 4 | 4/3 | 4 |
| 11 | 35263744 | 4 | 4/3 | 4 |

Rows 4-7 are the same. For each `n` the minimum is taken over all `k`. With `e = 1`
(`k = 0`) the minimum ratio is 2 (`u` a 3-cycle, `D = 6`), so the gadget needs its
transposition. The recorded `D = 4` witnesses (one per `(n,k)`, checked at `n = 11`) are
relabelled S_3 gadgets: a 3-cycle of `u` meeting one transposition of `e`, with the rest of
`u` either agreeing with `e` or fixing points. Whether every minimiser has this shape was
not checked.

**Local search on larger sets (heuristic only).**  `gate_anneal.c` anneals `(e,u)` in
`Sym(n)`, keeping `e` an involution exactly, and minimises `D/n + 4 max(0, M0 - M/n)`.
`sweep.sh` runs four seeds, `3000 n` steps, `M0` in {0.10, 0.25}. The finished runs are in
`anneal_results.txt`.
* For `n = 32, 64` every best marked model found had `D/M >= 4/3`. The recurrent optimum
  `D/n = 0.375`, `M/n = 0.28125`, with per-relator supports `(0, k, 0, k)`, is a disjoint
  union of S_3 gadgets and exact mark-zero pieces.
* For `n = 128` (`M0 = 0.10`) the ratios were 4.2 to 7.7. At this budget the search is
  weaker than the trivial gadget union.
* Controls: with `M0 = 0` it reaches `D = 0` (at mark 0) at once. With one relator dropped
  (`n = 64`, each of the four) it still never reached `D = 0` with `M/n >= 1/4`. So the
  search is not certified to find marked exact solutions even of the subsystems.
* The runs `n = 256, 512` were stopped unfinished and are not recorded.

**Interpretation, and why this is belief-neutral.**  `(TWS1)` is exact but only for
`n <= 11`. It says nothing about `(TW2G4)`, because on so few points no model can realise
the long-scale monodromy that `kazhdan-sofic-models-carry-long-scale-monodromy` forces on
any sofic model. It was predicted, not discovered, that small models are pinned to a fixed
positive ratio. The S_3 gadget is the cheapest local obstruction: the image of `(e,u)` in
`S_3` satisfies `e^2`, `c^2` and `r_2` exactly and fails only `r_1` and `r_3`. This
explains why annealing optima have equal supports on `r_1` and `r_3`.

**Where brute force dies.**  Two things block this class of approaches.
* The invariant is `min D/M`, which is monotone non-increasing in `n` (take disjoint unions
  with fixed points). Exhaustive enumeration costs about `n!` per involution type and reaches
  only `n = 11`. Soficity needs this minimum to tend to 0, and the smallest `n` at which it
  could first drop is not bounded by anything proved here.
* Local search is only as good as its controls, and the controls fail at `n = 64`.

A negative outcome of either method is therefore not evidence of nonsoficity. A ratio below
4/3 at some `n` would not prove soficity either, but it would be the first model beating the
local gadget. None was found. The open asymptotic question stays with
`titz-witzel-kernel-sofic`.
