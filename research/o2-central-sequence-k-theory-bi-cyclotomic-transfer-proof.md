---
rg: 2
id: o2-central-sequence-k-theory-bi-cyclotomic-transfer-proof
kind: route
title: Green–Julg corner transfer through the O_2-absorbing central sequence algebras of O_2 and of its crossed product, with Cuntz comparison for the unit class
target: o2-central-sequence-k-theory-bi-cyclotomic-transfer
requires:
  - o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
  - izumi-rokhlin-approximately-representable-duality
---

**Inputs from the required nodes.**  From
`o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`:
- item 1 (from Szabó arXiv:1509.08380, Theorem 5.15(2) and Theorem 3.7): for a
  pointwise outer `G`-action on a unital Kirchberg algebra, the central sequence
  algebra contains a fixed unital `O_∞` and eigen-isometries of every character;
- item 2 (the Rokhlin criterion);
- item 3, `F_∞(A)^α = F_∞(B)^(α̂)` inside `B_∞ = A_∞ ⋊ G`;
- item 4 (the Ĝ-action on `K_0`).

**Standard inputs, not re-read.**
- (RS) Reindexation (Kirchberg's ε-test).  Let `A` be separable unital with
  `A ≅ A ⊗ O_2`, and `S ⊆ A_∞` separable.  Then `A_∞ ∩ (A ∪ S)'` contains a
  unital `O_2`.  Likewise, if `S` is `α_∞`-invariant, the eigen-isometries of
  item 1 can be taken in `A_∞ ∩ (A ∪ S)'`.  Averaging over `G` and polar
  decomposition make approximate eigen-isometries exact.
- (CU) Cuntz: two properly infinite full projections with equal `K_0`-class
  are Murray–von Neumann equivalent.
- (FC) A full corner of a unital C\*-algebra induces an isomorphism on `K_*`.
  Orthogonal \*-homomorphisms add on `K_*`.  Let `ρ` be a \*-homomorphism and
  `z` a partial isometry with `z*z ρ(·) = ρ(·)`; then `z ρ(·) z*` has the same
  `K_*`-map as `ρ`.
- (KS) Kishimoto: for pointwise outer `α` on simple unital `A`, `A ⋊ G` is
  simple, and purely infinite if `A` is.  If `x ∈ A` satisfies
  `x α_g(a) = a x` for all `a`, then `x*x` and `xx*` are central.  So `x = 0`
  or `α_g` is inner.
- (KP) A unital Kirchberg algebra that is KK-contractible is `O_2`.

**Step 0: `K_*(A_∞ ∩ A') = 0` when `A ≅ A ⊗ O_2`.**  Take a projection `P` or
a unitary `U` over `C = A_∞ ∩ A'`, and let `S` be its entries.  By (RS) pick
Cuntz isometries `s_1, s_2 ∈ C ∩ S'`.
- `P = Σ_i (s_i ⊗ 1) P (s_i ⊗ 1)*`, a sum of two orthogonal projections, each
  equivalent to `P`.  So `[P] = 2[P]`.
- `U = Π_i (Ad(s_i ⊗ 1)(U) + 1 − s_i s_i* ⊗ 1)`, and each factor has class
  `[U]`.  So `[U] = 2[U]`.

**Step 1: the isometries `y_g`.**
- α̂ is pointwise outer: if `α̂_χ = Ad w`, then `w ∈ A' ∩ B = C` by (KS),
  so `χ = 1`.  `B` is a unital Kirchberg algebra by (KS).
- By item 1 applied to `(B, α̂)`, there is an isometry `w ∈ B_∞ ∩ B'` with
  `α̂_χ(w) = χ(g) w`.  Write `w = Σ_h x_h u_h`; eigen-ness forces `w = x u_g`.
  - `u_h w = w u_h` gives `α_h(x) = x`.
  - `a w = w a` gives `a x = x α_g(a)`.
  - `w*w = α_g^(−1)(x*x) = 1`.
  So `y_g := x` works.  Conversely each such `y_g` gives `y_g u_g ∈ B_∞ ∩ B'`.
- For `f ∈ F^α`: `a y f y* = y α_g(a) f y* = y f α_g(a) y* = y f y* a`, using
  `α_g(a) y* = y* a`.  Also `y f y*` is fixed.  So `Ad y` maps `F^α` into
  itself.  On `F^α`, `Ad(y_g u_g) = Ad y_g`, since `u_g f u_g* = f`.

**Step 2: well-definedness, action, commuting, swap.**
- *Choices.*  If `y, y'` both implement `α_g`, then `z = y'y*` lies in `F^α`,
  with `z*z = yy*` and `z (y f y*) z* = y' f y'*`.  By (FC) the `K_*`-maps agree.
  For `φ` this is item 4.
- *Action.*  `y_g y_h` implements `α_(gh)`, and `y_1` may be a fixed central
  isometry, which acts trivially by (FC).
- *Commuting.*  By (RS), take `v_χ` in `A_∞ ∩ (A ∪ {y_g, y_g*})'`.  Then
  `v_χ y_g = y_g v_χ`, so `Ad v_χ ∘ Ad y_g = Ad y_g ∘ Ad v_χ`.
- *Swap.*  `v_χ ∈ A_∞ = (B_∞)^(α̂)` and `v_χ u_h = χ̄(h) u_h v_χ`, so
  `v_χ b = α̂_(χ̄)(b) v_χ` for `b ∈ B`.  So the `v_χ` are the implementing
  isometries `y` for `α̂`.  By Step 1 read backwards, the `y_g` are the
  eigen-isometries for `α̂`.
- *Exterior equivalence.*  If `β_g = Ad(c_g) ∘ α_g` with `c_g ∈ U(A)`, then
  `β_g = α_g` on `A_∞ ∩ A'`.

**Step 3: the transfer identity, and `N_φ = 0`.**  Let `C = A_∞ ∩ A'`, with
`G` acting by `α`, and unitaries `u_g ∈ C ⋊ G`.  For `λ ∈ Ĝ` put
`e_λ = |G|^(−1) Σ_g λ̄(g) u_g`.  These are orthogonal projections with sum
`1` and `u_h e_λ = λ(h) e_λ`.
- *Corner.*  `j(f) = f e_1` is an isomorphism from `C^α = F^α` onto
  `e_1 (C ⋊ G) e_1`.
  - It is multiplicative, because fixed elements commute with `e_1`.
  - It is injective: look at the coefficient of `u_1`.
  - It is onto: `e_1 c u_h e_1 = E(c) e_1`, where `E` averages over `G`.
- *Fullness.*  If `α_g(v) = μ(g) v`, then `v e_λ = e_(λμ) v`.  So `v e_λ` is a
  partial isometry from `e_λ` to `e_(λμ) vv* ≤ e_(λμ)`.  With `μ = λ̄`,
  `e_λ ≲ e_1`, so `e_1` is full.  By (FC), `j_*` is an isomorphism.
- *Identity.*  Let `i : F^α → C` and `k : C → C ⋊ G` be the inclusions.
  - `k ∘ i = Σ_λ ρ_λ`, with `ρ_λ(f) = f e_λ` mutually orthogonal.
  - Take `v` to be `λ̄`-eigen and `z_λ = v e_λ = e_1 v`.
  - Then `z_λ* j(v f v*) z_λ = e_λ f v*e_1 v e_λ = f e_λ`, since
    `v* e_1 v = e_λ`.
  - So `ρ_λ = Ad(z_λ*) ∘ j ∘ Ad v`, and by (FC)
    `k_* i_* = j_* Σ_λ φ_(λ̄) = j_* N_φ`.
- *Vanishing.*  `A = O_2`, so `K_*(C) = 0` by Step 0.  Then `i_* = 0` and
  `N_φ = j_*^(−1) k_* i_* = 0`.
- *Special case.*  `[Σ_g s_g s_g*] = N_φ[1]` by item 4.

**Step 4: `N_ψ = 0` under contractibility.**  `B` is a unital Kirchberg algebra
with `B ≃_KK 0`, so `B ≅ O_2` by (KP).  Run Step 3 for `(B, α̂)`.  Here
`C = B_∞ ∩ B'`, `C^(α̂) = F^α` by item 3, and the eigen-isometries are the
`y_g u_g`, which act on `F^α` as `Ad y_g` (Step 1).  Step 0 for `B` gives
`K_*(C) = 0`, so `N_ψ = 0`.

**Step 5: item 3.**  Let `w_0 = y_h v_λ`.  It is a `λ`-eigen isometry with
`a w_0 = w_0 α_h(a)`.  As in Step 2, every such isometry induces `φ_λ ψ_h` on
`M_*`, and `φ_λ ψ_h [1] = [w_0 w_0*]`.
- *(⟸)*  A unitary `w` as in item 3 satisfies `a w = w α_h(a)`, so
  `[1] = [ww*] = φ_λ ψ_h [1]`.
- *(⟹), setup.*  Write `p = w_0 w_0*` and `Θ = Ad w_0`, a \*-endomorphism of
  `F^α` with `Θ(1) = p`.
- *Properly infinite.*  Take fixed central isometries `t_1, t_2` with
  orthogonal ranges (item 1).  Then the `Θ(t_i)` are isometries from `p` onto
  orthogonal subprojections of `p`.
- *Full.*  Let `w_0'` be a `λ̄`-eigen isometry implementing `α_h^(−1)`.  Then
  `z = w_0 w_0'` is a fixed isometry in `A_∞ ∩ A'`.  For `f ∈ F^α`,
  `z f z* = Θ(w_0' f w_0'*) ∈ p F^α p`, so `f = z*(z f z*) z` lies in the
  ideal generated by `p`.
- *Conclusion.*  `1` is properly infinite and full.  By (CU) there is
  `c ∈ F^α` with `c*c = p` and `cc* = 1`.  Put `w = c w_0`.
  - `w*w = w_0* p w_0 = 1` and `ww* = c p c* = 1`.
  - `α_g(w) = λ(g) w`.
  - `w* a w = w_0* c* a c w_0 = w_0* a p w_0 = w_0* a w_0 = α_h(a)`.
- *At `λ = 1`.*  Lift `w*` to unitaries in `A` that are approximately fixed.
  Averaging over `G` and taking polar parts gives unitaries in `O_2^α` with
  `Ad → α_h`.  So `α_h` is strongly approximately inner.  The converse is the
  first bullet.
- *At `h = 1`.*  `w` is a `λ`-eigen unitary in `A_∞ ∩ A' ⊆ (B_∞)^(α̂)` with
  `w b w* = α̂_(λ̄)(b)`.  So `α̂_(λ̄)` is strongly approximately inner;
  conversely, a fixed implementing unitary gives such a `w`.
- *Rokhlin.*  Rokhlin iff `[1] = 0` is item 2 of the central-sequence node.
  If `α` is Rokhlin, Szabó Corollary 3.8 (quoted in
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin-proof`) gives
  `α ≃_cc α ⊗ id_(O_2)`.  By Step 2, `F^α` is unchanged.  Far-out copies of
  `1 ⊗ O_2` lie in `F^α ∩ S'` by (RS), and Step 0 gives `M_* = 0`.

**Step 6: item 4.**
- *Torsion.*  `(1 − y)[1] = 0` gives `N_ψ[1] = p[1]`, and `N_ψ[1] = 0` by
  Step 4.  Item 4 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, with
  Izumi I Theorem 4.6 as cited in
  `izumi-rokhlin-approximately-representable-duality`, gives Rokhlin, so
  `[1] = 0`.
- *Freeness.*  In `Λ`, `Φ_p(x) = Φ_p(y) = 0` while `1 ≠ 0`: `Λ` is free of rank
  `(p − 1)²` over `Z`.
- *CRT.*  Put `R = Z[ζ_p, 1/p]`.  Then `Λ[1/p] = R[y]/Φ_p(y)` and
  `Φ_p(y) = Π_k (y − ζ_p^k)`.  For `j ≠ k`, `ζ_p^j − ζ_p^k` is a unit times
  `1 − ζ_p`, which is invertible in `R` because `(1 − ζ_p)^(p−1)` is a unit
  times `p`.  So CRT gives `∏_k R` with `y = ζ_p^k = x^k` on factor `k`.
- *Lines.*  A character `(λ, h) = (χ_0^a, g_0^b)` has `q = ζ_p^(ab)`, so `q` is
  trivial on its line iff `ab = 0`.  The isotropic lines are `a = 0` and
  `b = 0`.
- *Localisation.*  On factor `j`, `1 − x^(−k) y = 1 − ζ_p^(j−k)` is invertible
  for `j ≠ k`.  So `(1 − x^(−k) y)[1] = 0` puts `[1]` in factor `k` after
  inverting `p`.

**Where the argument uses each hypothesis.**
- `A ≅ O_2`: Step 0 for `C = A_∞ ∩ A'`.
- Outerness: eigen-isometries, which give fullness of `e_1` and `φ`.
- `O_2 ⋊ G ≃ 0`: only Step 4, through (KP) and Step 0 for `B`.
