---
rg: 2
id: kl-counterexample-can-be-superperfect-quasisimple
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken two-generator superperfect and quasisimple
distinct_from:
  kl-counterexample-can-be-two-generator-simple: that reduces a failure to a simple coefficient group, whose Schur multiplier can be nonzero; this passes to its universal central extension, which has trivial first and second homology and is not simple when the multiplier is nonzero.
  kl-counterexample-can-be-finitely-presented-simple: that asks for a finitely presented simple counterexample and is open; this proves only that finite presentation passes from a simple counterexample to its universal central extension.
  universal-schur-injectivity-for-nonsingular-adjunctions: that is the universal degree-two injectivity statement; this shows that over the reduced coefficient groups every Schur kernel is zero for trivial reasons, so degree-two information of the coefficient group itself cannot certify a failure.
---

If `kervaire-laudenbach-nonsingular-conjecture` fails, it fails over a
two-generator group `S^` that is

* **superperfect:** `H_1(S^; Z) = H_2(S^; Z) = 0`;
* **quasisimple:** perfect, with `S^/Z(S^)` nonabelian simple and
  `Z(S^) = H_2(S^/Z(S^); Z)`;

and the failure is total: for a nonsingular `w^ in S^ * <t>` of exponent sum
`m`, all of `S^` dies in `(S^ * <t>)/<<w^>>`.

Consequently the conjecture holds for all groups if and only if it holds for
two-generator superperfect quasisimple groups.

**What the reduced counterexample must also satisfy.**

1. Every nontrivial quotient of `S^` is a central quotient `S^/N` with
   `N <= Z(S^)`, and every one of them is again a total-collapse
   counterexample. So `S^` has no nontrivial hyperlinear, MF or finite
   quotient (`kervaire-laudenbach-holds-for-hyperlinear`,
   `kervaire-laudenbach-holds-for-mf`).
2. `K_2(S^, w^) <= H_2(S^) = 0`. Over the reduced coefficient group the
   Schur kernel vanishes for trivial reasons, although the coefficient map
   kills everything. So Schur injectivity *for the coefficient group itself*
   does not imply coefficient injectivity. The implication
   `kl-failure-yields-a-schur-kill` changes the coefficient group, to a torus
   amalgam, before a killed class appears. `central-extension-kl-schur-criterion`
   is vacuous here, since its quotient hypothesis fails for `S = S^/Z(S^)`.
3. **Finite presentation passes up.** If the simple counterexample `S` is
   finitely presented, so is `S^`. So a positive answer to
   `kl-counterexample-can-be-finitely-presented-simple` gives a finitely
   presented superperfect quasisimple counterexample.

Novelty is not claimed. The universal central extension argument is
elementary, and the route writes it out from Hopf's formula alone.

DERIVATION
kl-superperfect-quasisimple-counterexample-proof
