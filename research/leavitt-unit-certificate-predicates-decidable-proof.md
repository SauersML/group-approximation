---
rg: 2
id: leavitt-unit-certificate-predicates-decidable-proof
kind: route
title: Reduce each certificate check to normal-form equality and a finite enumeration
target: leavitt-unit-certificate-predicates-are-decidable
requires: [binary-leavitt-unit-word-problem-decidable]
---

Everything below rests on the normal form of `binary-leavitt-unit-word-problem-decidable`.
It decides equality in `R`, hence in `G = R^x` once units carry their inverses.

* **DF.** A product in `F_2[G]` is a finite list of unit products. Cancelling equal normal
  forms in pairs yields the reduced support, and `= 1` means the support is exactly the
  identity. Matrices add finitely many such sums.
* **CA.** Here `sigma o tau` has memory `N.M = {nm}`, which is finite and computed by unit
  products. Any pattern on `N.M` extends to a configuration, so `sigma o tau = id` holds iff
  the composite rule returns the identity coordinate on all `|A|^|N.M|` patterns.
  `tau(x)|_Omega` depends only on `x|_(Omega.M)`, so `q` is a Garden of Eden iff none of the
  `|A|^|Omega.M|` assignments reproduces `q`. Both checks are finite enumerations; the code
  searches the second by exhaustive backtracking.
* **KL.** Free-product normal form means alternating nontrivial syllables. Merge adjacent
  units by multiplication and adjacent powers of `x` by addition, dropping trivial syllables;
  each merge uses only the word problem of `G`. A word is trivial iff its normal form is empty.
  Checking `c^(-1) prod_j h_j w^(e_j) h_j^(-1)` is one reduction, and `eps(w)` is a sum.

The completeness arguments are in the target claim.

**Implementation and validation.** `experiments/nonsofic-certificates/` implements all three
checks. It computes every equality in two independent ways:
1. the Diamond-lemma normal form;
2. prefix tables, i.e. the action on binary sequences with a generic tail, composed and added
   without the rewriting rules. `R` is simple, so this representation is faithful.

Dual mode recomputes every product by path 2 and raises on any disagreement.
`selftest.py` passed all 71 checks on MSI, job 438223 (2026-09-11). The artifact of the
target claim lists them; they include:
- 400 random products agreeing with `experiments/depth_one_paired_leavitt_return_search.py`;
- the rank-three lifts of `leavitt-rank-three-unit-lift` (with `u3 = v3 = g`);
- the 180-element group of the finite Drazin seed, recomputed inside `F_2[R^x]`, satisfying
  `T^4 = T^2`, `h = T^2`, `v = T^3` and `(Tf)^2 = 0`;
- `tau_a o tau_b = tau_(ab)` on random pairs;
- agreement of the Garden-of-Eden search with brute force.
