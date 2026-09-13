---
rg: 2
id: halvable-corner-projective-elementary-groups-nonsofic-proof
kind: route
title: Pass to the proper halvable corner s_0 t_0, whose corner homomorphism meets the scalars trivially
target: halvable-corner-makes-projective-elementary-groups-nonsofic
requires: [d-ary-leavitt-groups-nonsofic-over-finite-fields, sofic-passes-to-subgroups]
---

Take `s_0, s_1, t_0, t_1 ∈ eAe` with `t_i s_j = delta_ij e` and `s_0 t_0 + s_1 t_1 = e`, as in step 1 of
`halvable-corner-makes-elementary-groups-nonsofic-proof`.

1. **A proper halvable idempotent.** Put `e' = s_0 t_0`.
   - `e'` is idempotent: `s_0 t_0 s_0 t_0 = s_0 e t_0 = s_0 t_0`, since `s_0 ∈ eAe`.
   - `e' != 0`, because `t_0 e' s_0 = e != 0`.
   - `e' != 1_A`, because `e' s_1 = s_0 t_0 s_1 = 0`, while `s_1 != 0` (as `t_1 s_1 = e != 0`).
   - `e'A ≅ eA`: the maps `x -> s_0 x` from `eA` to `e'A` and `y -> t_0 y` from `e'A` to `eA` are mutually
     inverse, since `t_0 s_0 x = e x = x` and `s_0 t_0 y = e' y = y`.
   - Hence `e'A ≅ eA ≅ eA ⊕ eA ≅ e'A ⊕ e'A`, so `e'` is halvable.
2. **The corner groups are nonsofic.** `B' = e'Ae'` is a countable nonzero unital `k`-algebra carrying a
   unital binary Leavitt family (step 1 of the cited proof, applied to `e'`). By
   `d-ary-leavitt-groups-nonsofic-over-finite-fields` with `d = 2`, `EL_n(B')` is nonsofic for `n >= 2`.
3. **The corner homomorphism.** `kappa_n(g) = g + (1 - e') 1_n` defines an injective homomorphism
   `GL_n(B') -> GL_n(A)` sending `1_n + b E_ij` to `1_n + b E_ij`. So `kappa_n(EL_n(B')) <= EL_n(A) <=
   EL_(nd)(R)`, by steps 3–4 of the cited proof, which use only `e'` idempotent.
4. **Trivial intersection with the scalars.** Suppose `kappa_n(g) = lambda 1` with `lambda ∈ k^x`. Since
   `g (1 - e') 1_n = 0`, multiplying both sides by `(1 - e') 1_n` gives `(1 - e') 1_n = lambda (1 - e') 1_n`,
   so `(lambda - 1)(1 - e') = 0` in `A`. `1 - e' != 0` and `lambda - 1 ∈ k` is invertible unless it is `0`,
   so `lambda = 1`. Hence `kappa_n(EL_n(B')) ∩ C = 1` for every group `C` of central scalars.
5. **Conclusion.** The quotient map `EL_(nd)(R) -> EL_(nd)(R) C / C` is injective on `kappa_n(EL_n(B'))`, so
   the quotient contains a copy of the nonsofic group `EL_n(B')`. By `sofic-passes-to-subgroups`, it is
   nonsofic. QED

**Model tests.**
- `A = M_2(F_q)` has the normalized rank function, which vanishes on halvable idempotents, so no nonzero
  halvable `e` exists, and the hypothesis fails as it should. `EL_2(F_q)` is finite, hence sofic.
- `A = L_(F_2)(1,2)` with `e = 1`: `e' = s_0 t_0` is proper, and step 4 is what makes the argument work over
  fields with nontrivial `k^x`, e.g. `L_(F_3)(1,2)`, where `-1` is a central scalar.
