---
rg: 2
id: fpbs-finite-fibre-boundary-squares-atomic-class-audit
kind: claim
title: Audit of the finite-fibre boundary-square reduction; it survives, but the nonatomic clause of its Theorem 2 needs a nonatomic class; an atomic finite-fibre class is a constant multiple of counting measure on one orbit, and its crossing diagonal is never conservative, so Theorem 3 and Corollary 4 stand as stated
distinct_from:
  fpbs-finite-fibre-bb-classes-are-boundary-squares: that states the reduction. This audits it against the Bevilacqua--Bowen source, corrects one clause of its Theorem 2 (nonatomicity of lambda holds iff the class C is nonatomic, which its Setting does not assume), and proves that the atomic case cannot produce a conservative crossing diagonal, so the equivalence in its Corollary 4 is unaffected
  fpbs-invariant-boundary-squares-need-heavy-returns: that uses counting measure on the orbit of a loxodromic fixed pair as a calibration of its return budget (its Corollary 4.3). This uses atomic classes to test which hypothesis of the square criterion carries the load, and to show that the conservative part of an atomic square can be nonzero without being conull
---

**Status: a written proof (`research/fpbs-finite-fibre-boundary-squares-atomic-class-audit-proof.md`) over
elementary facts on hyperbolic groups.** It was produced by an audit lane (2026-09-19). The audit was meant to refute
`fpbs-finite-fibre-bb-classes-are-boundary-squares`, established on 2026-09-19. The audit failed to refute it.

## What was checked, and passed

1. **Theorem 3 hypotheses against the source.** Bevilacqua--Bowen, arXiv:2510.05459, was read from the TeX e-print.
   - The source defines PDR verbatim: "for a.e. x,y in X there exist x=x_1,...,x_n=y with (x_i,x_{i+1}) in
     Con(X^2)". Here Con is the conservative part of the Kaimanovich--Hopf decomposition. So a conservative square
     gives PDR with n = 2.
   - The source states "amenable and therefore limit-amenable", "if the action is amenable then the normalized cost
     is 1" and "every regular action is amenable". So Adams' theorem gives the limit-amenability and the
     normalized-cost hypotheses.
   - The proof of Theorem 8.1 takes an ergodic component, then a product with a Bernoulli shift for freeness, then
     the Poisson suspension. It uses no freeness or finiteness beyond infinite, non-atomic ergodic components.
   - The items labelled "Conjecture" in the source are a Lemma and a Theorem. Only their labels are misleading.
2. **Step 1 and Theorem 1.** The cocycle formula (1.1) and the invariance of `{mu_x finite}` are correct.
3. **Step 2.** `h(g^{-1} y) = r_g(y)^{-1} h(y)` gives invariance of `lambda = h lambda_0`. The argument that
   `lambda(U) = infinity` is correct: support, minimality, compactness, then no invariant probability.
4. **Step 3.** `g_* M_p = M_{g p}` holds, because the factors `r_g(gx)^{-1}` cancel. The upward transfer uses
   `M_{g^{-1}p}(A) = M_p(gA)` and disjointness of the sets `gA` for a wandering `A`. It is correct in both directions.
5. **Proposition 5.** Glimm--Effros gives an embedding of `E_0`. Uniform Bernoulli measure is invariant under partial
   injections with graph in `E_0`. Extension from a complete section and infiniteness by (F3) are correct.
6. **Downstream.** `fpbs-invariant-boundary-squares-need-heavy-returns` was checked in Lemma 1, the sphere-sum
   budget, the step that pulls out sphere maxima, and the atom argument of Corollary 4.2. No gap was found.

## The gap, and its repair

The Setting of the audited node assumes only that `(Z, mu)` is ergodic imp. Its Theorem 2 asserts that `lambda` is
nonatomic. Its proof says "nonatomic whenever C is", which is correct. The statement omits this condition, and it
fails when C is atomic.

**Theorem A (atomic finite-fibre classes).** Let `Gamma` be nonelementary hyperbolic, and let `(Z, mu, xi)` be as in
the audited node with a.e. finite fibres and an atomic class `C`. Then:
1. `lambda = c * (counting measure on Gamma x_0)` for one orbit `Gamma x_0` and some constant `c > 0`. In particular
   `lambda` is atomic, and `lambda(U) = infinity` still holds for every nonempty open `U`.
2. The conservative part of `(d^2 Gamma, lambda x lambda)` is the set of atoms `(x, y)` with infinite stabiliser.
   These are exactly the fixed pairs `{k^+, k^-}` of loxodromic elements `k` for which both points lie in
   `Gamma x_0`.
3. The dissipative part has positive (indeed infinite) measure. So the crossing diagonal `W` is never conservative.

**Example B (the conservative part can be nonzero).** Take `Gamma = (Z/2 * Z/2) * Z = <s> * <t> * <u>` and the
loxodromic `h = st`. Then `s h s = h^{-1}`, so `h^- = s h^+` lies in `Gamma h^+`. Let `Z = Gamma / <h>` with counting
measure and `xi(g<h>) = g h^+`. This is an ergodic imp action with finite fibres over an atomic class. Its square has
a nonzero conservative part, the orbit of `(h^+, h^-)`, and an infinite dissipative part. `Z` is not PDR, because the
Con relation joins only cosets inside the virtually cyclic group `Stab{h^+, h^-}`. Also `beta_1^(2)(Gamma) = 1`, so
`Gamma` has cost `> 1`.

**Consequences for the audited node.**
- Theorem 2 should read "nonatomic if and only if C is nonatomic".
- Corollary 4 stands as stated. Item 1 can hold only with a nonatomic class, by Theorem A.3, and item 2 assumes
  nonatomicity.
- Theorem 3 needs its nonatomic hypothesis. Example B shows that the conservative part of an atomic square can be
  nonzero on a group of cost `> 1`. Nonatomicity is therefore not a formal hypothesis: BB's "non-atomic ergodic
  components" condition is doing work.

No new claim with `invalidates:` is recorded. None of the routes on the flagship cone breaks.
