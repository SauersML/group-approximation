---
rg: 2
id: sfts-without-two-sided-faults-rigidity-proof
kind: route
title: Each determining normal gives a rule in an open half-plane; compactness gives finitely many rules with a uniform margin, and the determinism closure then grows through every Euclidean ball
target: sfts-without-two-sided-faults-are-quantum-rigid
requires:
  - determinism-closure-certifies-quantum-rigidity
  - sft-crossed-product-fp-iff-quantum-rigid
---

Notation is as in the target. `|·|` is the Euclidean norm, `B^E_R = {z ∈ Z^2 : |z| <= R}`, and `B^∞_R` is the sup-norm
ball. Rules and the closure `C` are those of `determinism-closure-certifies-quantum-rigidity`:
- a *rule* is a finite `F ⊆ Z^2 \ {0}` such that, among patterns on `F ∪ {0}` occurring in `Ω`, the `F`-part
  determines the symbol at `0`;
- `C` is the least symmetric set containing `B^∞_(2D)` that is closed under
  (w) `v + F ⊆ C ⇒ v ∈ C` and (z) `v − F ⊆ C ⇒ v ∈ C`, for rules `F` with `F ∪ {0}` inside a translate of `B^∞_D`.

## Step 1. Determining normals are rules in open half-planes, and conversely

**(⇒)** Let `n` be determining, and put `H = {z : ⟨z,n⟩ < 0}`.
- The restriction `Ω → A^H` is continuous and injective on a compact space, so it is a homeomorphism onto its image.
- So `x ↦ x(0)` is a continuous function of `x|_H`. Hence it depends on `x|_F` for some finite `F ⊆ H`.
- `F` is a rule: two patterns on `F ∪ {0}` occurring in `Ω`, say in `x` and `y`, with equal `F`-parts have
  `x(0) = y(0)`.

**(⇐)** Let `F` be a rule with `⟨f, n⟩ <= −η' < 0` for all `f ∈ F`, and let `x, y ∈ Ω` agree on `{⟨z,n⟩ < t}`.
- For `⟨z,n⟩ < t + η'` the set `z + F` lies in `{⟨·,n⟩ < t}`.
- By translation invariance of the rule, `x(z) = y(z)`. So `x` and `y` agree on `{⟨·,n⟩ < t + η'}`.
- Iterating, `x = y`. So `n` is determining.

## Step 2. Finitely many rules with a uniform margin

For a rule `F` let `U_F = {u ∈ S^1 : ⟨f,u⟩ < 0 for all f ∈ F}`; this set is open since `F` is finite.
- By hypothesis and Step 1, `S^1 = ⋃_F (U_F ∪ −U_F)`.
- By compactness, finitely many rules `F_1, …, F_m` suffice.
- The function `g(u) = max_i max(min_(f∈F_i) −⟨f,u⟩, min_(f∈F_i) ⟨f,u⟩)` is continuous and positive on `S^1`. Let
  `η = min g > 0`.
- Let `ρ = max_(i, f ∈ F_i) |f|`. Then `η <= ρ`.

## Step 3. The closure is Z^2

Take `D >= ρ`, so that each `F_i ∪ {0} ⊆ B^∞_ρ(0) ⊆ B^∞_D(0)`, and `2D >= R_0 := ρ²/η + ρ`.

**Claim.** If `B^E_R ⊆ C` with `R >= R_0`, then `B^E_(R + η/4) ⊆ C`.
- Let `v ∈ Z^2` with `R < |v| <= R + η/4`, and put `u = v/|v|`. Choose `i, ε` with `⟨f, εu⟩ <= −η` on `F_i`.
- **Case `ε = +1`.** For `f ∈ F_i`:
  `|v + f|² = |v|² + 2|v|⟨f,u⟩ + |f|² <= |v|² − 2η|v| + ρ²
            <= R² + ηR/2 + η²/16 − 2ηR + ρ² = R² − (3/2)ηR + η²/16 + ρ² <= R²`.
  The last step uses `(3/2)ηR >= (3/2)(ρ² + ηρ) >= ρ² + η²/16`. So `v + F_i ⊆ B^E_R ⊆ C`, and (w) gives `v ∈ C`.
- **Case `ε = −1`.** The same computation for `−v`, with `⟨f, −u⟩ <= −η`, gives `−v ∈ C`, so `v ∈ C` by symmetry.

**Conclusion.**
- The base case holds: `B^E_(R_0) ⊆ B^E_(2D) ⊆ B^∞_(2D) ⊆ C`.
- Induction on `k` gives `B^E_(R_0 + kη/4) ⊆ C` for all `k`. So `C = Z^2`.
- Item 1 of `determinism-closure-certifies-quantum-rigidity` makes `Ω` `D`-quantum rigid.
- `sft-crossed-product-fp-iff-quantum-rigid` gives finite presentation over every field, taking `D` also at least the
  radius of `Ω`. ∎ (items 1–2)

## Step 4. Two-sided faults (items 3 and 4)

**Item 3.** Let `n^⊥` be a two-sided fault. A rule inside `{⟨·,n⟩ < 0}` or inside `{⟨·,n⟩ > 0}` would make `n` or
`−n` determining, by Step 1 (⇐). So no such rule exists. The argument of item 3 of
`determinism-closure-certifies-quantum-rigidity` uses only this fact:
- (w) at a point `v` beyond the current extreme level `⟨v,n⟩ > M` needs a rule with `⟨f,n⟩ < 0` throughout;
- (z) at such a point needs `⟨f,n⟩ > 0` throughout.

So `C ⊆ {|⟨t,n⟩| <= max over the initial ball of |⟨t,n⟩|}`.

**Item 4(b).** The wall certificate of `sft-crossed-product-fp-iff-quantum-rigid` refutes `D`-rigidity once the strip
width exceeds `2D`. A wall line is a two-sided fault.
- Glue `x` on one closed side of the strip with `y` on the other. This is legal once the strip is wider than the radius.
- The glued point agrees with `x` on a half-plane containing the strip and differs from it beyond, so the normal
  pointing away from that half-plane is not determining.
- Gluing the other way shows the same for the opposite normal.

**Item 4(c), slabs.** Let `x ≠ y` agree outside `S = {|⟨t,n⟩| <= c}`. Put `E_a(z) = diag([x(z)=a], [y(z)=a])` on the
side `{⟨t,n⟩ >= −c}`, and conjugate by any `g ∈ GL_2` on `{⟨t,n⟩ < −c}`.
- Off `S` the two coordinates agree, so the operators there are scalar and conjugation changes nothing.
- The family is therefore diagonal in one basis, hence commutative. It satisfies (Q1)–(Q3) and refutes nothing.

Walls, not slabs, are what the two-dimensional certificate detects.

**Corollary on fixed-point tile sets.** Suppose a determinism closure contains `B_(R(D))` (ℓ¹) with `R(D) > 2D`. Then
for every `n` it leaves the slab `{|⟨t,n⟩| <= max_(B_(2D)) |⟨t,n⟩|}`, since `max_(B_R) |⟨t,n⟩| = R|n|_∞` is increasing
in `R`. By item 3 there is no two-sided fault, and item 1 applies directly. ∎
