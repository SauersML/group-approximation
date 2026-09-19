---
rg: 2
id: mod-s2-prime-to-three-torelli-constituents-are-large
kind: claim
title: In an honest representation of Mod(S_2) putting a separating twist within eps of a cube-root scalar, every irreducible Torelli constituent of dimension n prime to three has n arcsin(eps/2) at least pi d_inf, and no determinant argument does better
distinct_from:
  mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit: that treats Torelli-abelian representations, all of whose Torelli constituents have dimension 1; this treats constituents of any dimension n of arbitrary honest representations, and at n = 1 recovers exactly its bound (TA1). It uses that node's definitions of W, d and d_inf, not its census.
  mod-s2-near-scalar-reps-reduce-to-torelli-abelian: that asks for a reduction to constituents of dimension 1; this proves that a reduction to constituents of dimension n prime to three with n eps -> 0 already suffices (together with d_inf > 0), so the reduction can be weakened.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the gap; this is a conditional bound per constituent that splits the gap into d_inf > 0 and a small-constituent statement, and it does not prove the gap.
  deligne-sector-determinants-see-only-dimension-mod-three: that kills determinant and winding invariants of Sp_4-level Deligne sector models; this is the analogue one level down, for determinants of Torelli constituents extended to finite-index subgroups of Mod(S_2), with the sharp constant of those arguments.
  mod-s2-finite-image-near-scalar-reps-are-torelli-abelian: that shows finite image forces every constituent to have dimension 1; this makes no finiteness assumption and gets only a dimension bound.
---

**ESTABLISHED** through `mod-s2-prime-to-three-torelli-constituents-are-large-proof`. Unreviewed; no novelty
claimed.

**Notation.**
- `M = Mod(S_2)`, `K` its Torelli group, `pi : M -> Gamma = Sp_4(Z)`, `t_s` the separating twist,
  `omega = exp(2 pi i/3)`.
- `W(Gamma')`, `d(Gamma')` and `d_inf` are as in `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`.
- `rho : M -> U(D)` is an honest (exact) finite-dimensional unitary representation, and
  `eps = ||rho(t_s) - omega I||_op < 2`.
- **Torelli constituents.** The algebra `A = span rho(K)` is a finite-dimensional C*-algebra. Its minimal
  central projections `e_1, ..., e_r` split `C^D = (+)_i V_i` with `V_i = C^(n_i) (x) C^(m_i)` and
  `rho(k)|V_i = sigma_i(k) (x) 1`, where `sigma_i : K -> U(n_i)` is irreducible. The `sigma_i` are the Torelli
  constituents, `n_i` their dimensions and `m_i` their multiplicities.
- `H_i = { g in M : rho(g) e_i rho(g)^* = e_i }`, a finite-index subgroup containing `K`, and `Gamma_i = pi(H_i)`.

**Statement.**

1. **(PC1) Extension.** For each `i` there is a finite-index `Gamma''_i <= Gamma_i` such that `sigma_i` extends to
   an honest unitary representation `P''_i` of `M''_i = pi^(-1)(Gamma''_i)`. If `m_i = 1` one may take
   `Gamma''_i = Gamma_i`.
2. **(PC2) Constituent bound.** If `3` does not divide `n_i`, then
   ```text
   n_i * arcsin(eps/2)  >=  pi * d(Gamma''_i)  >=  pi * d_inf .
   ```
   The same holds with `omega^(-1)` in place of `omega`. At `n_i = 1` this is exactly (TA1):
   `eps >= 2 sin(pi d_inf)`.
3. **(PC3) Unconditional case.** If `m_i = 1`, `3` does not divide `n_i`, and the block stabilizer `Gamma_i`
   contains `Gamma(3)` or `Gamma(4)` (in particular if it contains `Gamma(2)`), then
   `n_i arcsin(eps/2) >= pi/30`. If `rho(K)` acts irreducibly (one block, `m = 1`), then `n arcsin(eps/2) >= pi/15` whenever `3` does not divide `n = D`.
4. **(PC4) Structure of counterexamples.** Suppose (TAP) `d_inf > 0`
   (`mod-s2-torelli-abelian-census-limit-is-positive`) holds. Then in every honest `rho` with `eps < 2`, every
   Torelli constituent has dimension divisible by `3` or of dimension at least
   `pi d_inf / arcsin(eps/2)`, which is about `2 pi d_inf / eps`. So a family refuting
   `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap` under (TAP) must have all its prime-to-three
   Torelli constituents of dimension growing at least like `1/eps`.
5. **(PC5) Decomposition.** Let (SB) be `mod-s2-cube-root-reps-have-small-prime-to-three-constituents`:
   if `1/3 in Z_hon`, then `inf n_i arcsin(eps/2) = 0` over honest `rho` with `eps < 2` and their Torelli
   constituents with `3` not dividing `n_i`. Then
   ```text
   mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap   <=>   (TAP) and (SB).
   ```
   Also `mod-s2-near-scalar-reps-reduce-to-torelli-abelian` implies (SB), because Torelli-abelian constituents
   have `n = 1`. So (SB) is a weaker replacement for that reduction in any route to the gap: it asks only for
   some constituent of dimension prime to three and `o(1/eps)`, not for a whole Torelli-abelian representation.
   Whether it is strictly weaker is not known.
6. **(PC6) Kill: determinants of Torelli constituents see only `n mod 3`, and (PC2) is their sharp bound.**
   Call an argument *determinant-type* if, from each constituent, it uses only `n_i` and the values on
   separating twists of characters of finite-index `M'' >= K` that restrict on `K` to a power of
   `det sigma_i`. Such data are the conditions `theta^(i) in W(Gamma'')^perp` for
   `theta^(i)_c = n_i/3 + n_i h_i(T_c)`, where `h_i(T)` is the mean eigen-angle of `omega^(-1) sigma_i(T)` over
   `2 pi`. Then:
   - if `3 | n_i`, the data are consistent with `sigma_i(T) = omega I` exactly, so they give no bound;
   - if `3` does not divide `n_i`, the data at level `Gamma''` are consistent with
     `eps = 2 sin(pi d(Gamma'')/n_i)`, so (PC2) is the exact optimum of every determinant-type argument;
   - uniformly, they are consistent with `sigma_i(T) = zeta I` for `zeta` the `n_i`-th root of unity nearest
     `omega`, at distance `2 sin(pi/(3 n_i))`.
   Invariant: the determinant of an extended constituent sees the cube-root mark only through `n_i mod 3`,
   matching the order-three Deligne class. Every determinant-type argument dies at the step
   "`3 | n_i`, or `n_i >= c/eps`". In particular no such argument proves
   `mod-s2-near-scalar-reps-reduce-to-torelli-abelian`, (SB) or the gap: it cannot exclude representations whose
   Torelli constituents all have dimension divisible by 3, or all have dimension at least `1/(3 eps)` or so.
