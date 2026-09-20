---
rg: 2
id: thompson-t-not-mf-via-projective-unitary-gap
kind: route
title: Reduce Thompson's T not MF to the single projective-unitary gap, by deriving the orthogonal and symplectic gaps from it through generic perturbation in SU conjugacy classes
target: thompson-t-has-full-mf-radical
requires: [thompson-t-witnesses-are-dense-in-simple-adjoint-groups, thompson-t-unitary-gap-implies-orthogonal-and-symplectic-gaps, thompson-t-gap-on-dense-projective-unitary-images, thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes]
---

*Distinct from* `thompson-t-not-mf-via-classical-adjoint-trichotomy`. That route requires the SU, SO
and Sp gaps as three separate holes. This route requires only the SU gap. The other two are supplied
by the ESTABLISHED implication `thompson-t-unitary-gap-implies-orthogonal-and-symplectic-gaps`.

**The route.**
- Let `eps_SU` be the constant of `thompson-t-gap-on-dense-projective-unitary-images`.
- By `thompson-t-unitary-gap-implies-orthogonal-and-symplectic-gaps`, `Gap_T(SO)` holds with
  constant `eps_SU / 2`, and `Gap_T(Sp)` holds with constant `eps_SU`.
- Now run `thompson-t-not-mf-via-classical-adjoint-trichotomy` with `eps = eps_SU / 2`:
  - Suppose `T` were MF.
  - `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes` gives nontrivial irreducible pairs
    `sigma_n` with `D(sigma_n) -> 0`.
  - Item 1 of `thompson-t-witnesses-are-dense-in-simple-adjoint-groups` then gives dense
    `tau_n : Z/4 * Z/3 -> Inn(X(k))` with `D(tau_n) <= 2 D(sigma_n)`.
  - At least one of the three gaps is then violated. This is a contradiction.

**Composed constant.** For an orthogonal witness, the two factors of 2 compose. So a sequence
`sigma_n` with `D(sigma_n) -> 0` yields dense projective-unitary homomorphisms `tau'_n` with
`D_su(tau'_n) <= 4 D(sigma_n) + o(1)`.

**Exactness.**
- The target implies `Gap_T(SU)`, by item 1 of `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`.
- So `T` is not MF if and only if `Gap_T(SU)` holds.
- The route loses nothing.

**Where the difficulty now sits.** Everything has been moved into one family.
- **The family.** Homomorphisms `Z/4 * Z/3 -> PSU(k)` with dense image.
- **To prove the target**, show that the three Lochak--Schneps relators cannot all be
  operator-norm small on such a homomorphism. The bound must be uniform in `k`.
- **To refute the target**, exhibit one sequence of dense `PSU(k_j)`-homomorphisms on which all three
  relators become small. By the implication, no orthogonal or symplectic sequence can do anything a
  unitary one cannot.
