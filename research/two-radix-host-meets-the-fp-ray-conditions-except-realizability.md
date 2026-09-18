---
rg: 2
id: two-radix-host-meets-the-fp-ray-conditions-except-realizability
kind: claim
title: The two-radix odometer host is a finitely presented near group on N with the shift, a finitely generated non-virtually-abelian index kernel and infinite supports, but its index kernel is not realizable
distinct_from:
  fp-ray-near-actions-with-the-shift-exist: that asks for all five properties at once; this gives a finitely presented example with the first four and proves the fifth (realizability) fails for it.
  subshift-full-groups-give-infinite-order-twisted-near-shells: those near groups are realizable-in-question but not finitely presented (LEF); this near group is finitely presented but not realizable. So the two known failure modes are complementary.
artifacts:
  - research/artifacts/gq-bh-bh-shell-arith-lsf-mixed-radix.md
---

**ESTABLISHED** (lane proof, not reviewed; no novelty claimed).

Let `H` be the two-radix odometer host of `two-radix-odometer-host-is-f-infinity-with-fg-charge-kernel`
(coprime `h_0, h_1 >= 2`, `X = {0,1} x Zh`), and `chi` its near index.

1. **A genuine action on a line.** Every leaf `(eps, lam + Mt) -> (eps', mu + M'(t+g))` maps integers of
   its domain cone bijectively onto integers of its target cone. So `H` acts genuinely on
   `J = {0,1} x Z`. Under `beta(eps, q) = 2q + eps`, the element `s` is the translation `n -> n+1` of `J = Z`.
2. **The ray near action.** Restricting to `N = beta^-1(Z_(>=0))` gives `nu: H -> NearSym(N)`. It is
   injective, because `N` is dense in `X` and elements of `H` are continuous. It has `nu(s) = ` shift, and
   its index is `chi`.
3. **The conditions of `fp-ray-near-actions-with-the-shift-exist`, except the last.**
   - `H` is finitely presented (it is `F_infinity`).
   - `P = ker chi` is finitely generated.
   - `P` is not virtually abelian: it contains the carry-free group `W`, which contains Higman--Thompson
     groups.
   - Every nontrivial element of `P` moves a nonempty open set, which contains infinitely many points
     of `N`.
   - `s^-1 nu(g) s = nu(s^-1 g s)`, with `Ad(s^-1)` an automorphism of `P`.
4. **Realizability fails.** Take pairwise disjoint cones `c', d_0, d_1`. Then `a_(d_0) a_(c')^-1` and
   `a_(d_1) a_(c')^-1` lie in `P` and commute. On `N` they drain the progression `N ∩ c'` into
   `N ∩ d_0` and `N ∩ d_1` respectively, and fix everything else. By
   `commuting-translations-sharing-an-inflow-ray-are-not-realizable`, `nu|P`, and the restriction to any
   finite-index subgroup of `P`, has no realization.
5. **Scope.** Inside `J` there is no other choice of ray: an `s`-forward-invariant set commensurate with
   a ray is `beta^-1(Z_(>=n_0))`. So `H` does not resolve `fp-ray-near-actions-with-the-shift-exist`.
   Candidates for that claim must avoid commuting pairs of ray translations that share an inflow ray.
   On the ray of nonnegative integer points, any full group containing localized odometers on three
   pairwise disjoint cones has such a pair in its index kernel.
