---
rg: 2
id: nv-point-germ-groups-embed-in-zn-by-slope-proof
kind: route
title: Deep bricks around a fixed point are mapped to bricks around the same point, so the slope decides the germ, and iterating a canonical compression converges to a fixed point
target: nv-point-germ-groups-embed-in-zn-by-slope
requires: []
---

Notation and the facts used are those of Section 0 of
`research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`: deep bricks, sub-bricks,
the slope cocycle, and the rule that if `g` is canonical on `B ∋ x` of shape `k`, then
`gB` is the brick of shape `k - s(g,x)` containing `gx`. The only import is
Delorme–Guichardet, in item 6, cited exactly as in that artifact (Bekka–de la
Harpe–Valette, *Kazhdan's Property (T)*, Theorem 2.12.4).

**Item 1.**
- *Homomorphism.* For `g, h ∈ Stab_G(x)`, the cocycle identity gives
  `s(gh,x) = s(g,hx) + s(h,x) = s(g,x) + s(h,x)`.
- *Zero slope means locally trivial.* Let `gx = x` with `s(g,x) = 0`. Take a brick
  `B = [u] ∋ x` of shape at least `D_g` in every coordinate. Then `g` is canonical on
  `B`, and `gB` is the brick of shape `|u|` containing `x`, which is `B` itself. So
  `g ∘ φ_B = φ_B`, and `g` is the identity on `B`.
- *The kernel is exact.* Conversely an element that is the identity on a neighbourhood
  of `x` is canonical on a small brick around `x` with image that brick, so its slope
  is `0`. Hence `ker h_x` is exactly the subgroup of locally trivial elements, and
  `Germ_G(x) ≅ h_x(Stab_G(x)) <= Z^n`, which is free abelian.
- *Rank.* Suppose `s(g,x)_i = d_i < 0`. With `B = [u]` as above, `gB = [v]` has
  `|v_i| = |u_i| - d_i > |u_i|`. Both `u_i` and `v_i` are prefixes of `x_i`, so
  `v_i = u_i q` with `|q| = -d_i >= 1`. Write `x_i = u_i t`. Then `(gx)_i = v_i t = u_i q t`,
  and `gx = x` forces `t = qt`, so `t = q^∞`. If `d_i > 0`, apply the same argument to
  `g^{-1}`, whose slope at `x` is `-d`. So `h_x(Stab_G(x))` lies in the coordinates
  where `x_i` is eventually periodic.

**Item 2.**
- For `γ ∈ Stab_Γ(x)`, `ρ(γ)` fixes `ι(x)`, so `γ -> s(ρ(γ), ι(x))` is a homomorphism by
  item 1.
- If it vanishes on `γ`, then `ρ(γ)` is the identity on a neighbourhood `N` of `ι(x)`
  in `C^n`. So `γ` is the identity on the neighbourhood `ι^{-1}(N ∩ Z)` of `x`.
- The kernel therefore lies in the locally trivial subgroup, and `Germ_{Γ,X}(x)` is a
  quotient of the image, a subgroup of `Z^n`.

**Item 3.**
- `M_A = diag(1, A)` with `A ∈ SL_2(Z[1/p])` fixes `[1:0:0]`, and `A -> M_A` is
  injective into `PGL_3(Q_p)`, since `M_A` is scalar only if `A = I`.
- A non-scalar `M ∈ GL_3(Q_p)` is not the identity on any nonempty open
  `U ⊆ P^2(Q_p)`. Its fixed set is the union of the projectivized eigenspaces
  `P(ker(M - λ))` over eigenvalues `λ ∈ Q_p`: finitely many proper projective
  subspaces. Each is closed with empty interior (in an affine chart it lies in the
  zero set of a nonzero affine-linear function, and every nonempty open subset of
  `Q_p^2` contains points off such a line). A finite union of closed nowhere dense
  sets is nowhere dense.
- So `SL_2(Z[1/p])` injects into the germ group at `[1:0:0]`, which is therefore
  non-abelian.
- By item 2, no `ρ: SL_3(Z[1/p]) -> nV` and equivariant homeomorphism onto a closed
  invariant subset exist.

**Item 4.**
- Pick `z ∈ Z ∩ B` and write `z_i = w_i t_i`. By canonicity, `g(w_1t_1,…,w_nt_n) = (w_1u_1t_1,…,w_nu_nt_n)`.
  Since `gB = [wu]` is a sub-brick of `B`, the sub-brick rule makes `g` canonical on
  `[wu^j]` with image `[wu^{j+1}]` for every `j`. By induction
  `g^k z = (w_1u_1^k t_1, …, w_nu_n^k t_n)`.
- The coordinates with `u_i` nonempty converge to `w_i u_i^∞`. The others are constant
  and equal to `w_i t_i`. So `g^k z -> p ∈ B`, and `p ∈ Z` because `Z` is closed and
  `g`-invariant.
- `p ∈ B` and `u_i u_i^∞ = u_i^∞` give `gp = p`.
- `s(g,p) = |w| - |wu| = -|u|`, and `|u| ≠ 0` because `gB ≠ B`.

**Item 5.**
- `d = 0` is item 1.
- If `d <= 0` and `d ≠ 0`, take `B ∋ z` of shape `k` with every `k_i >= D_g`. Then `gB`
  is the brick of shape `k - d >= k` containing `gz = z`. A brick containing `z` of a
  coordinatewise larger shape lies inside `B`, and it is strictly smaller since
  `k - d ≠ k`. So `gB ⊊ B`.
- If `d >= 0`, use `s(g^{-1}, z) = -s(g, g^{-1}z) = -d`.
- For `n = 1` every nonzero `d` has a sign, so saddles need `n >= 2`.

**Item 6.**
- `h_x|_L: L -> Z^n ⊆ R^n` is a homomorphism, that is, a 1-cocycle for the trivial
  orthogonal representation on `R^n`.
- By Delorme–Guichardet there is `F ∈ R^n` with `h_x(g) = F - F = 0` for all `g ∈ L`.
- Item 1 then shows every `g ∈ L` is the identity near `x`. ∎

**Reformulation of slope-principality.** If `Z` is slope-principal, item 4 shows that
no `g` is canonical on a brick `B` meeting `Z` with `gB ⊊ B`. Conversely, if some
fixed point has a nonzero slope of constant sign, item 5 produces such a compression.
