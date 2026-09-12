# lx-cartan-b — the Cartan formula for the odd-primary reduced powers

Owns `CharClass/OddPComp*`, `OddPCartan*`, `OddPProduct*`.  Items 1–3, 5, 9 and 10 of the lemma list went to helper
lanes at ~10:50: lx-prodeval, lx-prodaw, lx-compbreal, lx-cartanvanish and lx-cartantorus.  This lane keeps items 4, 6, 7
and 8.  Deliverables are consumed by lx-pzero (`OddPTotal.PtotMulOddP`) and lx-cartantorus (`totalOf_oddDClass_cup`).

## Settled mathematics (agreed with lx-design and lx-pzero, 09-12)

* D-form Cartan in every degree: `[D_i(u⌣v)] = Σ_{a+b=i, a≤pq, b≤pq'} κ(a,b) [D_a u][D_b v]`, with
  `κ(a,b) = (−1)^{q q' p(p−1)/2} · wdPhi p a b 1 1 · (−1)^{b(pq−a)}`.
* Consumers need `P_tot := Σ_{j even} [D_j]` multiplicative on even classes, V on degree-2 classes (lx-cartanvanish,
  landed) and the T² corner (lx-cartantorus).  V' (vanishing above the range) is not built and not needed.
* The riffle Koszul exponent against `u⊗v⊗u⊗v⊗⋯` is exactly `q' q · p(p−1)/2`.

## Files

| file | content | state |
|---|---|---|
| `OddPProductEval` | `tupEvalAll`, indicators, `tupAllMod_eq_of_eval`, `tupEvalAll_tupDAll` | **GREEN**: probe 0912-121549-78818 printed BUILT; the on-main bytes at 4797f6f1d, which add a peer's file-level `open scoped Classical`, compiled in 0912-121839-91652 by cache restore |
| `OddPCompA` | `awNat`, `compA`, `compA_zero`, `tupEval_compA`, `tupEval_compA_oddD` | on main, unverified (a9e09d859) |
| `OddPCompB` | `compBAll`, `compBGen`, `compBLin`, `tupIncl_compBLin_oddDiff_single`, `compB`, `compB_zero` | attic (93ad5d44b) |
| `OddPCompare` | `compHomotopy`, T²-invariance and the augmentation, cochain and class comparison at a variable simplex degree, `cartanCochainA_eq_oddD` | attic (audit fixes landing) |
| `OddPCartanTotal` | `riffle_exp_eq`, `totalClass`, `cartanCochainB_eq_sum`, `totalClass_oddD_cup`, `totalOf_oddDClass_cup`, `ptotOf_mul`, `OddPTotal.ptotMulOddP` | attic (audit fixes landing) |

## GREEN
* `OddPProductEval`, probe 0912-121549-78818 (BUILT, axioms `[propext, Classical.choice, Quot.sound]`); cache-compiled at 0912-121839-91652.

## NEEDS (blocking the first compile of CompA → CartanTotal)
* lx-diag: `OddPDiagonalAug` green, on the closure of compA.
* lx-compbreal: CB4 `compBSum_mem_range`, CB5 `tupAllMap_compBSum`, CB6 `compBSum_zero_psiW_zero`, CB7 `tupEvalAll_compBSum` (CB1–CB3 authored).
* lx-prodaw: probe of `OddPProductAW` / `OddPProductAWDiag`.

## SPLIT
* none open.

## TRAPS
* zsh: `"${B}:path"`, never `"$B:path"`.
* `git grep -E` has no `\b`, so a declaration grep with `\b` silently finds nothing.
* Singular simplices have no `DecidableEq`: an `if σ = τ` needs `open Classical in` on the definition and on every statement.
* `rw [smul_eq_mul]` rewrites only the first smul instantiation, so a goal `a • x = a • y` needs `simp only [smul_eq_mul]`.
* A landing script hashes the shared-tree file at landing time.  A peer's edit made between probe and landing lands unprobed bytes, so re-probe the on-main blob.
* Main was mass-deleted at 11:10:52 by becc912bd (27762 paths) and restored forward at 3f71a3a50.  The clobber guard then refuses re-landings until `NM_BASE=<origin sha>` is given.
