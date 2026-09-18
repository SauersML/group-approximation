---
rg: 2
id: pisot-number-slope-stein-groups-are-contracting-rsgs-proof
kind: route
title: One integrality step (depth absorbs the denominators at the primes over β) extends the Pisot-unit finite-nucleus proof to all Pisot numbers with (F); homology of Z[1/β] ⋊ Z is finite for non-units; affine charts force slopes into β^Z
target: pisot-number-slope-stein-groups-are-contracting-rsgs
requires:
  - pisot-stein-groups-are-contracting-rsgs
  - pisot-unit-slope-stein-groups-are-finitely-presented
  - stein-v-groups-act-with-type-a-on-breakpoints
  - contracting-rsgs-embed-in-fp-simple-groups
---

The notation is that of `pisot-stein-groups-are-contracting-rsgs-proof`:
- `len(z)` is the length of a finite greedy expansion;
- `σ` runs over the non-identity embeddings, with `ρ_σ = |σ(β)| < 1`;
- `D = ⌊β⌋`.

Write `m(c) = min{m ≥ 0 : β^m c ∈ Z[β]}` for `c ∈ Z[1/β]`.

## 1. The coding exists exactly under (F)

- **Membership.** `Fin(β) ⊆ Z[1/β] ⊆ Γ_β`.
- **If some `a ∈ Γ_β ∩ (0,1)` is not in `Fin(β)`:**
  - The rotation `r_a` (`x ↦ x + 1 − a` on `[0,a)`, `x ↦ x − a` on `[a,1)`) lies in `V_β`.
  - `π^{−1}(a)` is a single point of `X_β`, since only points of `Fin(β)` are doubled.
  - So `r_a` is discontinuous there: left limit `1`, right value `0`.
- **Two ways this happens.**
  - If `β` is not an algebraic integer, `Γ_β ⊋ Z[1/β]`. Then `{g}` for `g ∈ Γ_β ∖ Z[1/β]` is such an `a`.
  - If `β` is an algebraic integer, then `β = a_1 + a_2β^{−1} + … + a_dβ^{1−d}` from its minimal polynomial,
    so `Γ_β = Z[1/β]`, and such an `a` exists iff (F) fails.
- **Converse.** (F) makes every point of `Γ_β ∩ (0,1)` a cylinder endpoint, which is step 1 of the unit
  proof verbatim.
- **Pisot.** (F) forces `β` to be Pisot (Frougny–Solomyak, as quoted in the SRS survey).

## 2. Length lemma with integrality

- **Claim.** For every `C` there is `L(C)` such that: if `z ∈ Z[1/β] ∩ [0,1)`, `n ∈ Z`, `β^n z ∈ Z[β]` and
  `|σ(z)| ≤ C ρ_σ^{−n}` for all `σ`, then `len(z) ≤ n + L(C)`.
- **Proof.** Put `y = β^n z ∈ Z[β]`, so `|σ(y)| ≤ C`.
  - If `n ≥ 0`, split the greedy expansion of `y` into its integer part `I ∈ Z[β]` and `F = y − I ∈ Z[β] ∩ [0,1)`.
    - `|σ(F)| ≤ C + D/(1−ρ_σ)`, and `Z[β]` is a lattice in Minkowski space, so `F` lies in a finite set.
    - Each point of that set has finite length by (F).
  - If `n < 0`, then `y ∈ Z[β] ∩ [0,1)` itself lies in a finite set.
  - In both cases `len(z) ≤ n + len(F)` (with `F = y` if `n < 0`). ∎
- The only change from the unit proof is the hypothesis `β^n z ∈ Z[β]`, which is automatic for units.

## 3. Slope defect

Fix `f ∈ V_β`, a cone `[w]` inside one piece `x ↦ β^k x + c`, and `J = f(I_w)`. Suppose `b` with
`len(b) ≤ L` is interior to `J`. Then `p = β^{−k}(b − c)` is interior to `I_w`, so `len(p) > |w|`.
- **Coarse boundaries** are those with `L < L_1(c) := max(L_0(c), m(c))`, where `L_0(c)` is as in the unit
  proof. There are finitely many, so for `|w| ≥ N(f)` none is interior to `J`.
- **Fine boundaries** are those with `L ≥ L_1(c)`.
  - Integrality: `β^{k+L} p = β^L b − β^L c ∈ Z[β]`, since `β^L b` is a digit polynomial and `L ≥ m(c)`.
  - Size: as in the unit proof, `|σ(p)| ≤ C_β ρ_σ^{−(k+L)}`.
  - Step 2 gives `len(p) ≤ k + L + L_β`. Hence `L > |w| − k − L_β`.
- **Conclusion.** The same bound as for units: the local slope exponent `e` lies in the fixed interval
  `[−L_β, log_β(ℓ_max/ℓ_min)]`, independent of `f`.

## 4. Offsets and nucleus

The local action at a deep cone is `ω ↦ d + β^e π(ω)` with `d = β^{|ō|}(β^k a_w + c − a_ō)`.
- `β^{|ō|+k} a_w = β^e · β^{|w|} a_w ∈ β^e Z[β]`.
- `β^{|ō|} c ∈ Z[β]` once `|ō| ≥ m(c)`, which holds for deep `w` because `|ō| ≥ |w| − k − L_β`.
- `β^{|ō|} a_ō ∈ Z[β]`.
- So `d ∈ β^{−L_β} Z[β]`, a lattice. The unit proof's bound on `|σ(d)|` holds unchanged, so `d` ranges over
  a finite set.

Steps 5 (finite nucleus, `X_β` an irreducible SFT since `d_β(1)` is finite) and 6 (other lengths) are
verbatim. Fullness and finite presentation (BBMZ Theorem A) are as in
`pisot-unit-slope-stein-groups-are-finitely-presented`, step 1, with `Fin(β) = Z[1/β] ∩ [0,1)`.

**Type (A).** Apply `stein-v-groups-act-with-type-a-on-breakpoints`:
- (F1) is finite presentation;
- (F2) is finite presentation for every other length.

This gives item 2.

## 5. Non-units: finite abelianization (item 3)

Put `Γ = Z[1/β]`, and let `A` be multiplication by `β`. Tanner's form of Li's Prop. 5.5, valid for every
algebraic `λ`, gives `H_0 = Γ/(1−β)Γ` and `H_1 = H_2(Γ ⋊ Z)`. The groupoid homology is independent of `ℓ`
(Tanner, Cor. `cor hom best`).
- **`H_0`.** `β ≡ 1` is invertible mod `β − 1`, so `Γ/(1−β)Γ = Z[β]/(β−1) ≅ Z/|f(1)|`, where `f` is the
  minimal polynomial. This is finite.
- **`H_1`.** It is an extension of `ker(A − 1) = 0` by `coker(Λ²A − 1)` on `Λ²Γ`.
  - `Λ²Γ = ∪_n (Λ²A)^{−n} Λ²Z[β]`. Every `(Λ²A)^{−n}x` is congruent to `x` mod `(Λ²A − 1)Λ²Γ`, so
    `Λ²Z[β]/(Λ²A − 1)` surjects onto `coker(Λ²A − 1)`.
  - `Λ²Z[β]/(Λ²A − 1)` is finite iff no product `β_iβ_j` (`i < j`) of distinct conjugates equals 1. Such a
    product would make `β_i` a unit, hence `β` a unit.
- **Conclusion.** The AH sequence `H_0 ⊗ Z/2 → V^ab → H_1 → 0` makes `V^ab` finite. `D(V)` is simple
  (Tanner), of finite index, and finitely presented.
- **Degree 2.** `β² = aβ + b` gives `|f(1)| = a + b − 1`. Also `Λ²Γ = Z[1/b]` with `Λ²A = det A = −b`, so
  `H_1 = Z[1/b]/(1+b) = Z/(b+1)`.

## 6. Quadratic criterion and fields (item 4)

- **(F) for quadratics.**
  - Hollander (survey Thm. `srsbeta`) with `d = 1`: for minimal polynomial `X² − aX − b`, (F) holds iff
    `r_0 = b/β ∈ D_1^{(0)} = [0,1)`, i.e. `0 ≤ b < β`.
  - `D_1^{(0)} = [0,1)` is elementary: for `0 ≤ r < 1`, `τ_r(z) = −⌊rz⌋` satisfies `|τ_r(z)| < |z|` for
    `z > 0` and `0 ≤ τ_r(z) ≤ |z|` for `z < 0`; so `|τ_r²(z)| < |z|` for `z ≠ 0`.
  - Irreducibility excludes `b = 0`.
  - Pisot and `b ≥ 1` force `b ≤ a`: the conjugate `(a − √(a²+4b))/2` exceeds `−1` iff `b < a + 1`.
  - Conversely `1 ≤ b ≤ a` gives `β > a ≥ b`.
- **Fields.** Given non-square `D > 1`, put `c = ⌊m√D⌋` and `β = c + m√D`. Its minimal polynomial is
  `X² − 2cX − (Dm² − c²)`, so `a = 2c` and `b = Dm² − c² = (m√D − c)(m√D + c)`.
  - `b ≥ 1` since `D` is not a square, and `b < m√D + c < β`, which gives (F).
  - For `m = 1`, `b ≥ 2` unless `D = c² + 1`.
  - For `D = t² + 1` and `m = 2`, `c = 2t` and `b = 4`.

## 7. Affine codings carry one slope (item 5)

- **Local actions of powers.** Let `[w] ∋ x_0` be a deep cone with `h^n([w])` inside the neighbourhood where
  `h^n` is affine of slope `γ^n`. The local action `h^n|_w` is `chart_ō^{−1} ∘ h^n ∘ chart_w`, affine of
  slope `γ^n β^{t_n}` for some `t_n ∈ Z`, since the charts have slopes in `β^Z`.
- **They are distinct.** For `n ≠ n'` these slopes differ, because `γ^{n−n'} ∉ β^Z`.
- **Conclusion.** Contraction puts all of them in one finite nucleus. So `G` is not contracting.
- **`V_{2,3}` has the required germs.** One element with a slope-3 germ at 0 is
  `[0,1/9) → [0,1/3)` (slope 3), `[1/9,5/9) → [1/3,2/3)` and `[5/9,1) → [2/3,1)` (slope 3/4). For a slope-2
  germ, use `[0,1/4) → [0,1/2)` (slope 2) and `[1/4,1) → [1/2,1)` (slope 2/3). Since 2 and 3 are
  multiplicatively independent, they cannot both lie in one `β^Q`, so at least one germ has slope outside
  `β^Q` for any `β`. ∎
