---
rg: 2
id: relative-defect-finite-compression-core-proof
kind: route
title: Confine the kernel to a compression core, then quotient by the finite kernel
target: relative-defect-criterion-holds-for-finite-compression-cores
requires:
  - sofic-quotients-by-finite-normal-subgroups-are-sofic
  - sofic-groups-kill-rigid-compression-defects
---

1. **Confinement.** `M` is normal in `H`, so for all `n >= 0`
   `M = t^n M t^-n <= t^n Gamma t^-n`. Similarly `M = h M h^-1 <= h Gamma h^-1`.
2. **Finite core.** If `K_t(Gamma)` is finite, so is `M`.
   - `H/M` is sofic, by `sofic-quotients-by-finite-normal-subgroups-are-sofic`.
   - `Gamma/M <= G/M` is a rigid pair of `H/M`. Images of Kazhdan groups are
     Kazhdan, and the compressor semigroup of `Gamma` maps into that of
     `Gamma/M`, so it still generates `G/M`.
   - `[z, Gamma] <= M` says that `zM` centralizes `Gamma/M`. The absolute
     criterion `sofic-groups-kill-rigid-compression-defects` gives
     `[g z g^-1, gamma] M = M`.
3. **Theorem E.** Put `R_+ = F_q[x_1..x_d]` and `R = F_q[x^(+-1)]`.
   - `A = L L^T`, where `L` is the lower unitriangular matrix with all
     sub-diagonal entries `1`. So `A_ij = min(i,j)`, `det A = 1`, and every
     entry of `A` is at least `1`.
   - `A` maps `N^d` into itself. So the element of `SL_d(Z)` acting by
     `x^v -> x^(Av)` conjugates `e_ij(f)` to `e_ij(A.f)` and maps `EL_r(R_+)`
     into itself. `A N^d` misses `e_1`: `Av = e_1` forces `sum v_j = 1`, so
     `v = e_k` and `(Av)_2 = min(2,k) != 0`. So `A` is a strict compressor.
   - `A^n Gamma A^-n = EL_r(S_n)`, where `S_n` is the span of the monomials
     `x^w` with `w` in `A^n N^d`. Hence every element of `K_A(Gamma)` has
     entries in the span of the monomials whose exponents lie in all the sets
     `A^n N^d`.
   - A nonzero `w` in `A^n N^d` is `A^n v` for a nonzero `v` in `N^d`. Every
     entry of `A` is at least `1`, so `|Av|_1 >= d |v|_1`, and therefore
     `|w|_1 >= d^n`. So only `w = 0` lies in all the sets `A^n N^d`, the
     entries are constants, and `K_A(Gamma) <= GL_r(F_q)`, which is finite.
   - A nonzero ideal `I` of `R` contains `x_1^(-N) f` for any nonzero `f` in `I`
     and any `N`. So `EL_r(R, I)` contains `e_12` of a non-polynomial entry, and
     it does not lie in `Gamma`.
4. **Constraints on a counterexample.**
   - `M` is infinite, by 2.
   - `H/M` carries a nontrivial rigid defect, so it is nonsofic by the absolute
     criterion.
   - A splitting `H = M semidirect Q` would embed `H/M` in the sofic group `H`.
   - If `H` is residually finite and `M` is closed in the profinite topology,
     then `H/M` is residually finite.
