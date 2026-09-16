---
rg: 2
id: fpbs-amenable-outer-kernel-forces-price-one-proof
kind: route
title: Centralize the inner-acting part into an infinite amenable normal subgroup of the preimage and lift through wq-normality twice
target: fpbs-amenable-outer-kernel-forces-price-one
requires:
  - fpbs-wq-normal-price-one-subgroup-forces-price-one
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

Complete proof. It is Section 2 of the linked artifact.

**Definitions.**
- Write `pi : Gamma -> Q = Gamma/N` and `c_gamma(u) = gamma u gamma^-1`.
- Use the intermediate-subgroup definition of wq-normality from
  `fpbs-wq-normal-hull-is-almost-malnormal`.

**Two elementary facts.**
- **(i)** If `N ◁ Gamma` is infinite and `N <= Lambda`, then `Lambda` is
  wq-normal in `Gamma`. For every proper `K ⊇ Lambda` and every
  `g notin K`, `g K g^-1 ∩ K ⊇ N`.
- **(ii)** An infinite normal subgroup is wq-normal. The argument is the
  same.

**Proof.** Let `Lambda = pi^-1(A)` and `C = C_Gamma(N) ∩ Lambda`.
1. **`pi(C) = A`.**
   - Let `gamma in Lambda`. Then `pi(gamma) in ker rho`, so there is `a in N`
     with `c_gamma = c_a` on `N`.
   - Then `a^-1 gamma in C` and `pi(a^-1 gamma) = pi(gamma)`.
   - Also `pi(C) <= A`.
2. **`C` is infinite and amenable.**
   - `C ∩ N = C_Gamma(N) ∩ N = Z(N)` is abelian, and `C/Z(N) ≅ A`.
   - So `C` is an extension of an abelian group by an infinite amenable group.
     It is amenable and infinite.
3. **`C` is normal in `Lambda`.**
   - For `lambda in Lambda`, `lambda C_Gamma(N) lambda^-1 = C_Gamma(lambda N lambda^-1) = C_Gamma(N)`,
     since `N ◁ Gamma`.
   - Also `lambda Lambda lambda^-1 = Lambda`.
4. **`Lambda` has fixed price one.**
   - By (ii), `C` is an infinite amenable wq-normal subgroup of `Lambda`.
   - The stated consequence of `fpbs-wq-normal-price-one-subgroup-forces-price-one`
     applies. It covers every countable group with an infinite amenable
     wq-normal subgroup, and its proof route cites Ornstein--Weiss.
5. **`Gamma` has fixed price one.**
   - `Lambda ⊇ N` is infinite, and wq-normal in `Gamma` by (i).
   - The same claim lifts fixed price one from `Lambda` to `Gamma`.

**Consequences.**
- **Semidirect products.** If `phi` has order `k` in `Out(N)`, then the outer
  kernel of `N semidirect_phi Z` is `kZ`, which is infinite cyclic.
- **Locally finite quotients.** If `Q` is locally finite, then `ker rho` is
  locally finite, hence amenable. So it suffices that `ker rho` be infinite.
