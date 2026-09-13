---
rg: 2
id: sl3z-cocompact-quotient-uniquely-ergodic-minimal-proof
kind: route
title: Zariski density, unipotents escaping to the identity, and Benoist-Quint give minimality and unique ergodicity
target: sl3z-cocompact-quotient-uniquely-ergodic-minimal
requires:
  - benoist-quint-zariski-dense-invariant-measures-are-haar
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-microstates-2026-09-13.md
---

Full proof: Proposition 2.1 of the artifact. Here `G = SL_3(R)`, `Γ = SL_3(Z)`, `X = G/Λ`.

1. **Zariski density.** A polynomial vanishing on `Γ` vanishes on `u_ij(Z)`. Along each line
   `t ↦ u_ij(t)` it is a polynomial with infinitely many zeros, so it vanishes on `u_ij(R)`, and these
   subgroups generate `G`. `G` is connected with simple Lie algebra.
2. **No finite orbit.** If `Γ·gΛ` is finite, its stabilizer has finite index and contains `u = u_12(n)`
   with `n >= 1`, so `w = g^(−1)ug ∈ Λ ∖ {1}`. With `a_t = diag(e^(−t), e^t, 1)` and `h_t = a_t g`,
   `h_t w h_t^(−1) = u_12(n e^(−2t)) → 1`. Write `h_t = f_t λ_t` with `f_t` in a compact `F`, `G = FΛ`. Then
   `λ_t w λ_t^(−1) = f_t^(−1)(h_t w h_t^(−1))f_t → 1`, which is impossible in the discrete set `Λ ∖ {1}`.
3. **Unique ergodicity.** An atom of an invariant probability measure has a finite orbit of atoms of equal
   mass. By 2 there are none, so Corollaire 1.2(a) gives Haar measure.
4. **Minimality.** An orbit closure is closed, invariant and infinite, so it is `X` by Corollaire 1.2(b). ∎
