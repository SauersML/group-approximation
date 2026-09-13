---
rg: 2
id: halvable-corner-makes-elementary-groups-nonsofic-proof
kind: route
title: The corner carries a unital binary Leavitt family, and the corner homomorphism exports its nonsofic groups
target: halvable-corner-makes-elementary-groups-nonsofic
requires: [d-ary-leavitt-groups-nonsofic-over-finite-fields, sofic-passes-to-subgroups]
---

1. **The family.** `End_A(eA) = eAe` acting by left multiplication, and `Hom_A(eA, eA ⊕ eA)` is
   the set of columns over `eAe`. Write an isomorphism as `x -> (t_0 x, t_1 x)` with inverse
   `(y_0, y_1) -> s_0 y_0 + s_1 y_1`. The composite `eA -> eA` is the identity iff
   `s_0 t_0 + s_1 t_1 = e`. The composite `eA ⊕ eA -> eA ⊕ eA` is the identity iff
   `t_i s_j = delta_ij e`. So the two formulations of the hypothesis agree.
2. **The corner algebra.** `B = eAe` is a unital `k`-algebra with unit `e`. It is nonzero because
   `e != 0`, and countable because `R` is. The four elements of step 1 form a binary Leavitt family
   in `B`, in the sense of the Lean structure `LeavittFamily`:
   - `t_i s_j = delta_ij 1_B`;
   - `s_0 t_0 + s_1 t_1 = 1_B`.

   By `d-ary-leavitt-groups-nonsofic-over-finite-fields` with `d = 2`, the groups `B^x`,
   `GL_n(B)` and `EL_n(B)` are nonsofic for `n >= 2`.
3. **The corner homomorphism.** Define `kappa_n : GL_n(B) -> GL_n(A)` by
   `kappa_n(g) = g + (1 - e) 1_n`.
   - The entries of `g` lie in `eAe`, so `g (1-e) 1_n = (1-e) 1_n g = 0`, and `(1-e) 1_n` is
     idempotent. Hence `kappa_n(g) kappa_n(h) = gh + (1-e) 1_n = kappa_n(gh)`.
   - `kappa_n(1_B 1_n) = e 1_n + (1 - e) 1_n = 1`.
   - `kappa_n` is injective, since `g = e 1_n kappa_n(g) e 1_n`.
   - `kappa_n(1_n + b E_ij) = 1_n + b E_ij` for `b ∈ B`, `i != j`. So
     `kappa_n(EL_n(B)) <= EL_n(A)`.

   The case `n = 1` embeds `B^x` in `A^x`.
4. **Unblocking.** `GL_n(A) = GL_n(M_d(R)) = GL_(nd)(R)`. For `a ∈ M_d(R)` and `i != j`, index
   rows by pairs `(i, p)`. Then `1 + a E_ij = prod_(p,q) e_((i,p),(j,q))(a_pq)`, because the factors
   are `1 + N` with `N` supported in the block `(i,j)`, and any two such `N` multiply to zero. So
   `EL_n(A) <= EL_(nd)(R)`.
5. **Conclusion.** `EL_n(B)` embeds in `EL_(nd)(R) <= GL_(nd)(R)`, so both are nonsofic by
   `sofic-passes-to-subgroups`. For `d = 1`, step 3 embeds `B^x` in `R^x`. QED
