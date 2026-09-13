---
rg: 2
id: z2-o2-implementing-cocycle-classes-are-path-components-proof
kind: route
title: Average a cocycle against a nearby one and take the polar part; connect classes by paths of unitaries in the K_1-trivial properly infinite central sequence algebra
target: z2-o2-implementing-cocycle-classes-are-path-components
requires:
  - o2-central-sequence-k-theory-bi-cyclotomic-transfer
  - z2-o2-actions-anti-inner-and-o3-rokhlin-criterion
  - o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences
---

**Standard inputs, not re-read.**
- (AI) Every automorphism of `O_2` is approximately inner (Rørdam; Kirchberg–Phillips).
- (U1) For a properly infinite unital C\*-algebra `D`, `U(D)/U_0(D) ≅ K_1(D)` (Cuntz).
- (LU) A unitary in `D_∞ = ℓ^∞(N, D)/c_0(N, D)` lifts to a sequence of unitaries.
  If `D` carries an involution `α` and the unitary is fixed (or anti-fixed), the
  lift can be taken fixed (or anti-fixed): average `(x_n ± α(x_n))/2` and take
  polar parts for large `n`.
- (CU) Cuntz: properly infinite full projections with equal `K_0`-class are
  Murray–von Neumann equivalent.

**From the required nodes.**
- Step 0 of `o2-central-sequence-k-theory-bi-cyclotomic-transfer-proof`:
  `F = A_∞ ∩ A'` contains a unital `O_2`, and `K_*(F) = 0`.
- Items 1 and 2(a) of `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`.
- Item 1 of `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences` (a fixed
  unital `O_∞` and odd isometries in `F`), and the Rokhlin property as a unital
  equivariant `(C(Z/2), shift) → (F, α)`.

**Step 1: rigidity.**  Let `D` be unital with an involutive automorphism `α`,
and `z, z' ∈ U(D)` with `zα(z) = z'α(z') = 1`, so `α(z) = z*`.
- `T(x) = z α(x) z'*` is a linear involution of `D`:
  `T²(x) = z α(z) x α(z'*) z'* = x`, since `α(z'*) z'* = (z' α(z'))* = 1`.
- `x_0 = (1 + T(1))/2 = (1 + zz'*)/2` satisfies `T(x_0) = x_0`.  Since
  `‖zz'* − 1‖ = ‖z − z'‖ < 2` and `zz'*` is normal, `−1 ∉ sp(zz'*)`, so `x_0` is
  invertible.
- Put `S = Ad(z') ∘ α`.  Then `T(x)*T(y) = z' α(x*y) z'* = S(x*y)`.  So
  `x_0*x_0 = S(x_0*x_0)`, and `|x_0|^(−1) ∈ C*(x_0*x_0)` is `S`-fixed.
- `v = x_0 |x_0|^(−1)` is unitary and
  `T(v) = zα(x_0)z'* · z'α(|x_0|^(−1))z'* = T(x_0) S(|x_0|^(−1)) = v`.
  So `vz' = zα(v)`, that is, `z' = v* z α(v)`.
- Since `‖z − z'‖ ≤ 2` always, distinct classes are at distance exactly `2`.

**Step 2: classes are components.**  `F` contains a unital `O_2`, so it is
properly infinite.  With `K_1(F) = 0` and (U1), `U(F)` is path connected.
- If `z' = v*zα(v)`, a path `v_t` from `1` to `v` gives the path
  `v_t* z α(v_t)` in `Z`.
- A path in `Z` is uniformly continuous, so it splits into finitely many steps
  of length `< 2`.  Step 1 makes consecutive points cohomologous.
- The class of `1` is `{v*α(v)}`, the coboundaries.

**Step 3: implementing cocycles.**  By (AI) there are `u_n ∈ U(A)` with
`Ad(u_n) → σ` pointwise; put `u = [(u_n)]`.
- For `a ∈ A`: `z_u a z_u* = u* α(u α(a) u*) u = u* α(σ(α(a))) u = u*σ(a)u = a`.
  So `z_u = u*α(u) ∈ F`.  Also `z_u α(z_u) = u*α(u)α(u)*u = 1`.
- If `u'` also implements `σ`, then `v = u*u' ∈ U(F)` and
  `z_(u') = v* z_u α(v)`.

**Step 4: spectral criteria.**
- *SAI ⟹ `z_α ∈ Z_0`.*  Invariant `u_n ∈ U(A^α)` give an invariant implementer,
  with cocycle `1`.
- *`z_α ∈ Z_0` ⟹ SAI.*  If `z_u = v*α(v)`, then `u' = uv*` has
  `z_(u') = v z_u α(v)* = 1`, so `α(u') = u'`.  Lift by (LU) to unitaries in
  `O_2^α`; they implement `σ` in the limit.
- *Spectral gap.*  If `−1 ∉ sp(z_u)`, then `‖z_u − 1‖ < 2` and Step 1 gives
  `z_u ~ 1`.  Conversely an invariant implementer has `z = 1`.  For unitaries,
  `‖u − α(u)‖ = ‖1 − z_u‖`, and `‖1 − z‖ < 2` iff `−1 ∉ sp(z)`.
- *Logarithm.*  If `z_u = exp(ih)` with `α(h) = −h`, put `v = exp(ih/2)`.  Then
  `α(v) = exp(−ih/2)` and `v* z_u α(v) = 1`.  Conversely `z = 1 = exp(0)`.
- *Explicit implementer.*  Applying `α` to `u α(a) = σ(α(a)) u` gives
  `α(u) a = σ(a) α(u)`.  So `h = (u + α(u))/2 = u(1 + z_u)/2` is `α`-fixed with
  `h a = σ(a) h`.  If `−1 ∉ sp(z_u)`, `h` is invertible, and `h*h ∈ F^α` since
  `h*σ(b) = b h*`.  Then `w = h|h|^(−1)` is fixed and unitary, and
  `w a w* = h a (h*h)^(−1) h* = σ(a) h (h*h)^(−1) h* = σ(a)`.

**Step 5: the sign.**
- `v* z α(v) = −1` iff `v*(−z)α(v) = 1`, so `z ~ −1` iff `−z ∈ Z_0`.  An
  implementer `u'` is odd (`α(u') = −u'`) iff `z_(u') = −1`.  So odd implementers
  exist iff `−z_α ∈ Z_0`, and (LU) turns them into approximately odd unitaries
  in `O_2`.
- `−1 ∈ Z_0` iff `−1 = v*α(v)` for some `v ∈ U(F)`, iff `α(v) = −v`.  By item 1
  of `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`, this is strong
  approximate innerness of `α̂`.
- *Odd logarithm of `−1`.*  If `exp(iπh) = −1` with `h = h*`, `α(h) = −h`, then
  `sp(h)` is a finite subset of `2Z + 1`.  The spectral projections satisfy
  `α(1_({k})(h)) = 1_({−k})(h)`.  So `Q = Σ_(k>0) 1_({k})(h)` is a projection in
  `F` with `α(Q) = 1 − Q`: a Rokhlin projection.  Conversely a Rokhlin
  projection `Q` gives `h = 2Q − 1`.

**Step 6: contractible crossed product.**  Item 2(a) of the anti-inner node
gives an odd implementer, so `z_α ~ −1` by Step 5.  Then SAI iff `−1 ∈ Z_0` iff,
by Step 2, `1` and `−1` are joined by a path in `Z`.  The last bullet of Step 5
excludes odd one-parameter groups unless `α` is Rokhlin.

**Step 7: `K_0`.**  Let `C = F ⋊_α Z/2 ⊆ (A ⋊_α Z/2)_∞` with symmetry `λ`, and
`p_z = (1 + zλ)/2` for `z ∈ Z`.  `(zλ)² = zα(z) = 1` and `(zλ)* = λz* = α(z*)λ = zλ`.
- *Equivalence.*  With `T` as in Step 1,
  `(1 + zλ) x (1 + z'λ) = (x + T(x))(1 + z'λ)`, so `p_z C p_(z') = Fix(T) p_(z')`.
  For `x ∈ Fix(T)`, `x*x` commutes with `z'λ` and `xx*` with `zλ`.  So
  `(xp_(z'))*(xp_(z')) = x*x p_(z')` and `(xp_(z'))(xp_(z'))* = xx* p_z`.  Since
  `y ↦ y p_z` is injective on `F`, `p_z ~ p_(z')` iff `Fix(T)` contains a
  unitary, iff `z ~ z'`.
- *Properly infinite and full.*  `p_1 C p_1 = F^α p_1 ≅ F^α` contains a unital
  `O_∞`.  An odd isometry `t ∈ F` gives `t* p_1 t = (1 − λ)/2 = p_(−1)`, and
  likewise `t* p_(−1) t = p_1`, so both are full; `p_(−1) C p_(−1) ≅ F^α` too.
  `Ad(u)` maps `C` onto itself, since `uλu* = σ_u(z_u*)λ` with
  `σ_u = Ad(u)|_F`.  Hence `p_(±z_u) = u* p_(±1) u` are automorphic images.
- By (CU), for `z, z' ∈ {±1, ±z_u}`, `z ~ z'` iff `[p_z] = [p_(z')]`.  Since
  `[1_C] = 0` (unital `O_2` in `F`), `[p_(−1)] = −[p_1]`.  With the full corner
  `F^α ≅ p_1Cp_1`, the case `z = 1`, `z' = −1` reads `2[1] = 0` in `K_0(F^α)`.

**Model test (inner action).**  For `σ = Ad(u)` with `u = u* ∈ U(O_2)`,
`Ad(u)` is trivial on `F`, so `Z` consists of the symmetries of `F`.  Step 1 with
`z = 1` shows the class of `1` is `{1}`; every other symmetry `s ≠ 1` has
`‖1 − s‖ = 2`.
