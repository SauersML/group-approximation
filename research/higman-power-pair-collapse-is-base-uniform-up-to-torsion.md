---
rg: 2
id: higman-power-pair-collapse-is-base-uniform-up-to-torsion
kind: claim
title: The power-pair collapse of Higman's group uses base two only through torsion, and for odd bases there are nontrivial quotients with infinite virtually cyclic edge image
distinct_from:
  higman-elementary-amenable-edge-images-collapse: that proves the dichotomy and the collapse for base two; this proves that the dichotomy and the power-pair closure hold verbatim for every base n, that for base n they force torsion generators rather than collapse, and that for odd n this is sharp.
  nontrivial-higman-quotients-keep-all-four-bs-subgroups: that is the base-two torsion lemma; this locates it as the only base-two input in the whole descent-chain programme.
  higman-bounded-derived-length-edge-images-collapse: that certifies derived length at most 11 for base two; this is a calibration across bases and does not reprove any derived-length case.
artifacts:
  - experiments/higman-base-n-calibration-2026-09-18/base_n_quotients.py
  - experiments/higman-base-n-calibration-2026-09-18/base_n_quotients-output.txt
---

**ESTABLISHED** (proposed) by `higman-power-pair-collapse-is-base-uniform-up-to-torsion-proof`.

**Setting.** For `n >= 2` let
`H4(n) = < a, b, c, d | b^a = b^n, c^b = c^n, d^c = d^n, a^d = a^n >` (`x^y = y^-1 x y`), so
`H4 = H4(2)`. For a quotient `Q` put `A_M = <a^M, c^M> <= Q` and `A = A_1`. Let `X` be the class of
`higman-elementary-amenable-edge-images-collapse` (the closure of finite, abelian and
free-subgroup-free locally indicable groups under extensions and directed unions; it contains every
elementary amenable group).

**Statement.**
1. **Base-uniform dichotomy.** For every `n >= 2`, every quotient `Q` of `H4(n)` and every `M >= 1`,
   `A_M` is free on `a^M, c^M` or `A_M / A_M'` is finite.
2. **Base-uniform closure.** For every `n >= 2`: if `A` lies in `X`, then some `A_M` is finite, and all
   four generators of `Q` have finite order.
3. **Base two.** For `n = 2` the last conclusion forces `Q = 1`. This is the only place in the
   dichotomy, the closure and the collapse where `n = 2` is used.
4. **Sharpness for odd bases.** For every odd `n >= 3`, `a, c -> (x,y) |-> (-x,y), (1-x,y)` and
   `b, d -> (x,y) |-> (x,-y), (x,1-y)` define a quotient `Q = D_oo x D_oo` of `H4(n)` whose edge image
   `A = <a,c>` is the infinite dihedral group: infinite, virtually cyclic, amenable, with `A/A'` finite
   and `A_2 = 1`. For every `n >= 3`, `(Z/(n-1))^4` is a quotient with nontrivial finite edge image.
5. **Structure of the base-two residue.** If `Q` is a nontrivial quotient of `H4` whose edge image `A` is
   not free-on-every-power (for example `A` amenable), then for every `M`: `A_M'` has finite index in
   `A_M`, so it is finitely generated; `A_M / A_M''` is virtually free abelian of finite rank; and
   `a, c` have infinite order while no `A_M` is finite.

**What it kills.** The whole descent-chain programme (tower invariants, the chain, the parity flip, the
dichotomy and the power-pair closure) is a theorem about `H4(n)` for every `n`. In base `n` odd it
cannot prove more than "the generators are torsion", because `D_oo x D_oo` exists. So:
- no argument that only uses the substitution lemma `ev(iota_b(w)) = b^-1 ev(w) b` and properties of
  `A` can prove that an infinite amenable (even virtually cyclic) edge image collapses;
- every extension of the collapse to amenable edge images must use base two, and through the
  power-perfect regime with **infinite-order** generators. The only known base-two input is the
  smallest-prime torsion lemma, which the chain reaches only after some `A_M` is finite.
- Hence the remaining case is exactly the base-uniform question: *does every amenable power-perfect pair
  `(A; a, c)` realized in a quotient of some `H4(n)`, with `a, c` of infinite order, have a finite power
  subgroup?* A counterexample in an odd base would show that base two must enter a second time.

**The finer invariant it points to.** By item 5 the next invariant is `b_1(A_M') = rank(A_M'/A_M'')`,
the rational abelianization of a finite-index subgroup. The chain controls `A_M/A_M'` (it is finite).
Showing `b_1(A_M') = 0` for all `M` is the next rung. It would still not collapse perfect edge images such
as simple amenable groups, which is why item 4's base-uniformity matters.
