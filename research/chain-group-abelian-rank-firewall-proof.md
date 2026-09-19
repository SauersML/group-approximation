---
rg: 2
id: chain-group-abelian-rank-firewall-proof
kind: route
title: Bass-Serre theory of the amalgam G_1 = BS(1,2) *_Z BS(1,2) bounds its abelian subgroups and computes the zoom centralizer, normal forms give free zoom-root pairs, the linearizing chart kills the smooth square map, and fundamental domains on both sides of the lift's fixed point give a global dyadic square map
target: chain-group-abelian-rank-firewall-for-germ-hosts
requires: []
---

Notation as in the target. `T` is the Bass-Serre tree of `G_1 = A *_C B`: vertices `gA`, `gB`, edges
`gC`. `G_1` acts without inversions, vertex stabilizers are conjugates of `A` and `B`, and edge
stabilizers are conjugates of `C ≅ Z`. `G_1` is torsion-free (an amalgam of torsion-free groups).

Model of each factor: `BS(1,2) = ⟨t, e | t e t^-1 = e^2⟩ ≅ Z[1/2] ⋊ Z`, acting faithfully on `R` by
`e ↦ (x ↦ x+1)` and `t ↦ (x ↦ 2x)`. In `A`, `t = s` and `e = δ`. In `B`, `t = δ` and `e = σ`, and
`N_B` is the translation subgroup `Z[1/2]`.

## Step 1. Abelian subgroups of BS(1,2)

**Lemma 1.** An abelian subgroup `H ≤ BS(1,2)` lies in the translation subgroup `Z[1/2]` or is
infinite cyclic.

*Proof.* Suppose `H` contains `g : x ↦ 2^k x + a` with `k ≠ 0`. Then `g` has the unique fixed point
`p = a/(1 - 2^k)`, and every `h ∈ H` commutes with `g`, so it fixes `p`. So
`h = (x ↦ 2^m (x - p) + p)` is determined by `m`. The map `h ↦ m` is an injective homomorphism
`H -> Z`, so `H ≅ Z`. ∎

## Step 2. Abelian subgroups of G_1 (Statement 1)

Let `H ≤ G_1` be abelian.

**Case (a): `H` contains a hyperbolic element `h`.**
- For `g ∈ H`, `g·Axis(h) = Axis(g h g^-1) = Axis(h)`. So `H` preserves the line `L = Axis(h)`.
- No `g ∈ H` reverses `L`: a reversal conjugates the translation `h|L` to its inverse, but `g h g^-1 = h`
  and `h` has nonzero translation length.
- So `H` acts on `L` by translations. This gives a homomorphism `ℓ : H -> Z` with `ℓ(h) ≠ 0`.
- `K = ker ℓ` fixes `L` pointwise, so it lies in the stabilizer of an edge of `L`, a conjugate of
  `C ≅ Z`. So `K = 1` or `K ≅ Z`.
- `H/K ≅ ℓ(H) ≅ Z` is free, so `H ≅ K × Z`. Hence `H ≅ Z` or `H ≅ Z^2`.

**Case (b): every element of `H` is elliptic.**
- *Common fixed points.* Let `g_1, …, g_n ∈ H`. Then `Fix(g_1)` is a nonempty subtree, and it is
  invariant under `g_2` because `g_2 Fix(g_1) = Fix(g_2 g_1 g_2^-1) = Fix(g_1)`. An elliptic automorphism
  preserving a subtree `S` fixes a point of `S`: if `g_2 v = v`, the nearest-point projection of `v` to
  `S` is `g_2`-fixed. So `Fix(g_1) ∩ Fix(g_2) ≠ ∅`, and it is again a subtree invariant under the
  others. By induction, `⟨g_1, …, g_n⟩` fixes a vertex.
- *Consequence.* Every finitely generated subgroup of `H` lies in a conjugate of `A` or of `B`. By
  Lemma 1 it is a finitely generated subgroup of `Z[1/2]` or infinite cyclic, so in all cases cyclic.
- So `H` is locally cyclic. It is torsion-free, hence isomorphic to a subgroup of `Q`.

**Exclusions.** `Z^3`, `Z^∞` and `Z[1/2] × Z` are abelian, not locally cyclic, and not `Z^2`.
`Z ≀ Z` contains `Z^∞`. Thompson's `F` contains `Z^n` for every `n`: elements with pairwise disjoint
supports commute. So none of them embeds in `G_1`. ∎

## Step 3. The zoom centralizer (Statement 2)

- *`N_B ∩ C = 1`.* In `B`, the quotient `B/N_B ≅ Z` sends `δ` to a generator. So `δ^k ∈ N_B` only for
  `k = 0`.
- *`Fix(σ) = {v_B}`, where `v_B = B`.* The edges at `v_B` are the cosets `bC` with `b ∈ B`, and `σ` fixes
  `bC` iff `b^-1 σ b ∈ C`. But `b^-1 σ b ∈ N_B`, since `N_B` is normal in `B`, and `N_B ∩ C = 1`. So `σ`
  fixes no edge at `v_B`. Since `Fix(σ)` is a subtree containing `v_B`, it is `{v_B}`.
- *Reduction to `B`.* If `g σ = σ g`, then `g Fix(σ) = Fix(σ)`, so `g v_B = v_B` and `g ∈ B`.
- *In `B`.* In the affine model, `σ = (x ↦ x+1)`, and `x ↦ 2^m x + a` commutes with it iff `2^m = 1`.
  So `C_B(σ) = N_B`.

Hence `C_(G_1)(σ) = N_B ≅ Z[1/2]`. ∎

## Step 4. Free zoom-root pairs (Statement 3)

The normal form theorem for `A *_C B`: a product `x_1 ⋯ x_m` with `m ≥ 1`, whose factors lie
alternately in `A ∖ C` and `B ∖ C`, is nontrivial.

- `σ^k ∈ B ∖ C` for `k ≠ 0`, since `σ^k ∈ N_B` and `N_B ∩ C = 1`.
- `ρ^(±1) ∈ A ∖ C`. In the affine model of `A`, `ρ = s^-1 δ s` is the translation by `1/2`, and `C` is
  the translation group `Z`.
- `s^(±1) ∈ A ∖ C`, since `s` maps to a generator of `A / ⟨⟨δ⟩⟩ ≅ Z`.

**Pair `⟨σ, e_1⟩` with `e_1 = ρ σ ρ^-1`.** Take a nontrivial reduced word in free letters `x ↦ σ` and
`y ↦ e_1`, and substitute `y^b ↦ ρ σ^b ρ^-1`. The result is an alternating product of syllables
`σ^a ∈ B ∖ C` and `ρ^(±1) ∈ A ∖ C`. Adjacent `y`-powers are separated by a nonzero `x`-power, so no
`ρ^-1 ρ` cancellation occurs. By the normal form theorem it is nontrivial, so
`⟨σ, e_1⟩ ≅ F_2`.

**Pair `⟨σ, τ⟩` with `τ = s^-1 σ s`.** Argue the same way, with syllables `σ^a` and `s^(±1)`.

**`ρ_meta ≠ 1`.** `[ρ, σ] = e_1 σ^-1` and `[ρ, σ^2] = e_1^2 σ^-2`. In the free group `⟨σ, e_1⟩` these two
elements do not commute. Commuting elements of a free group are powers of a common element. The element
`e_1 σ^-1` is primitive, so it is its own root, and `e_1^2 σ^-2` is not a power of it. So
`ρ_meta = [e_1 σ^-1, e_1^2 σ^-2] ≠ 1`.

Written out, the reduced alternating form is
`ρ σ ρ^-1 σ^-1 ρ σ^2 ρ^-1 σ^-1 ρ σ^-1 ρ^-1 σ^2 ρ σ^-2 ρ^-1`, with 15 syllables. ∎

## Step 5. Consequences for faithful germ maps (Statement 4)

Suppose `θ` is faithful. Then `θ : G_1 -> Q` is an isomorphism.

**(F2).** The centralizer of `θσ` in `Q` is `θ(C_(G_1)(σ)) = θ(N_B)`, by Step 3.
- `N_B = ∪_n ⟨r_n⟩` with `r_n^(2^n) = σ`.
- So every element is `r_n^k` for some `n, k`, and its `2^n`-th power is `σ^k`.

**(F3).** By Step 4, `⟨ρ, σ⟩ ⊇ ⟨σ, e_1⟩ ≅ F_2` and `⟨τ, σ⟩ ≅ F_2`. Neither is soluble, so their images
are not soluble.

**(F1).** By Step 2, `Q` has no `Z^3` and no `F`. The sparse-support form:
- *Hypothesis.* Suppose `1 ≠ g ∈ Q` and `K ≥ 1` are such that, for every `j ≠ 0`, the moved set `S` of
  a representative of `g` and its translate `S + jK` meet in a set bounded above.
- *Commuting conjugates.* Put `g_j = σ^(jK) g σ^(-jK)`. Its moved set is `S + jK`, and the moved sets
  are pairwise disjoint near `+∞`. Each moved set is invariant under its own element. So the `g_j`
  commute as germs.
- *Independence.* A finite product `∏ g_j^(n_j)` acts on `S + jK` (near `+∞`) as `g_j^(n_j)`. So it is
  the trivial germ only if every `g_j^(n_j)` is trivial.
- *Contradiction.* `g` has infinite order, because `Q ≅ G_1` is torsion-free. So `⟨g_j⟩ ≅ Z^∞`,
  contradicting Step 2.

So a faithful realization has **no** nontrivial germ of sparse support. This is the abstract form of
the mechanism in `scale-periodic-bs-chain-germ-representations-are-not-faithful`, where the defect `w_k`
is such a germ, or dies. ∎

## Step 6. The smooth model (Statement 5)

**The chart `u`.** Let `δ` be a doubling lift, `δ(x+1) = δ(x) + 2`, that covers a circle map `f`
topologically conjugate to `z ↦ 2z`.
- The conjugacy lifts to an increasing homeomorphism `u` of `R` with `u(x+1) = u(x) + 1` and
  `u δ u^-1 = 2x + c` for some `c ∈ Z`. Replacing `u` by `T_c u` makes `c = 0`.
- For `δ_f` this applies. `f` has slopes `1, 2, 4`, and the slope-1 piece `[0, 1/2)` is mapped onto
  `[1/2, 1)`, where the slopes are 2 and 4. So `f^2` has every slope `≥ 2`, `f` is an expanding
  degree-2 covering, and it is conjugate to doubling (Shub).

**The model.** In the `u`-chart put `σ' = x+1`, `δ' = 2x` and `s' = x^2` (germs at `+∞`).
- `s' δ' s'^-1 (y) = (2 y^(1/2))^2 = 4y = δ'^2(y)`, and `δ' σ' δ'^-1 (y) = y + 2`.
- So `(u^-1 s' u, δ, σ)` is a germ realization of the chain with the given `δ`.
- Its root is `ρ' = s'^-1 δ' s' = (2 x^2)^(1/2) = 2^(1/2) x`, which is affine.
- So `⟨ρ', σ'⟩` lies in the affine group `R ⋊ R_(>0)`. That group is metabelian, so its second derived
  subgroup is trivial, and `θ(ρ_meta) = 1`.
- By Step 4, `ρ_meta ≠ 1` in `G_1`. So this `θ` is not faithful, and it violates (F3).

**Uniqueness among power maps.** `s' = c x^a` satisfies `s'(2x) = 4 s'(x)` iff `2^a = 4`, that is,
`a = 2`. For every constant `c > 0`, `ρ' = s'^-1(2 c x^2) = (2 x^2)^(1/2) = 2^(1/2) x` again. So every
such model dies the same way.

The general solution of `s'(2x) = 4 s'(x)` is `s' = x^2 φ(log_2 x)` with `φ` 1-periodic and positive.
The step shows that the rigid choice `φ = const` is fatal. For the dyadic PL square map of
`non-affine-doubling-lifts-evade-the-sparse-defect-kill`, `φ` is not constant. Otherwise `ρ_meta` would
be the trivial germ, but the exact computation (`out_scout.txt`) shows it moving every point of a bulk
period at scales 3, 5 and 6. ∎

## Step 7. The host needs a global square map (Statement 6)

Setting: `δ_f(n + r) = 2n + d(r)` with `n ∈ Z` and `r ∈ [0,1)`. On `[0,1)`:
- `d(r) = r + 1/2` on `[0, 1/2)`;
- `d(r) = 2r` on `[1/2, 3/4)`;
- `d(r) = 4r - 3/2` on `[3/4, 1)`.

The square map of `fast.py` is the fundamental-domain map `s_0 : [4, 17/2] -> [16, 65]`, dyadic PL
through `(4,16), (8,48), (33/4,49), (17/2,65)`, extended by `s(δ_f^k x) = δ_f^(2k) s_0(x)`.

**(a) The recorded host is not a chain configuration.**
- `0 <= δ_f(x) - 2x = d(r) - 2r <= 1/2` for all `x`, so `δ_f^2(x) = 4x + O(1)`.
- If `a_f = T_12` near `-∞`, then near `-∞`,
  `a_f δ_f a_f^-1 = T_12 δ_f T_-12 = T_-12 δ_f = 2x + O(1)`, using `δ_f T_-12 = T_-24 δ_f`.
- These two maps differ unboundedly as `x -> -∞`. So `a_f b_f a_f^-1 ≠ b_f^2`, and `(a_f, b_f, x+1)`
  does not satisfy the chain relations in `Homeo(X)`.
- This does not show that `⟨V, b_f, a_f⟩` contains no chain configuration at all. It does show that the
  recorded one fails.

**(b) Fixed point.**
- Solve `n + r = 2n + d(r)`, that is, `n = r - d(r)`. The function `r - d(r)` equals:
  - `-1/2` on `[0, 1/2)`;
  - `-r ∈ (-3/4, -1/2]` on `[1/2, 3/4)`;
  - `3/2 - 3r ∈ (-3/2, -3/4]` on `[3/4, 1)`.
- It is an integer only at `r = 5/6`, where `n = -1`. So `x_0 = -1/6` is the unique fixed point.
- `δ_f - id` is nondecreasing, with slopes `0, 1, 3` on the three pieces. So it is `< 0` on
  `(-∞, x_0)` and `> 0` on `(x_0, ∞)`. Thus `δ_f` pushes every point away from `x_0`.
- On `[-1/4, 0)`, which contains `x_0`, `δ_f(x) = 4x + 1/2`, that is, `D_4` about `x_0`.

**(c) The global square map `s_f`.**
- *Right side `(x_0, ∞)`.* The intervals `δ_f^k [4, 17/2)`, `k ∈ Z`, tile `(x_0, ∞)`. Put
  `s_f = δ_f^(2k) s_0 δ_f^(-k)` on `δ_f^k [4, 17/2)`. This is well defined and continuous because
  `s_0(17/2) = 65 = δ_f^2(16) = δ_f^2(s_0(4))`. It agrees with the `fast.py` map `s` on `[4, ∞)`. So
  near `+∞`, `s_f` **is** the square map of the w16 computations.
- *Left side `(-∞, x_0)`.* Here `δ_f(-1/2) = -1` and `δ_f(-1) = -3/2`. Take
  `s_0^- (x) = 2x + 1/2` on `[-1, -1/2]`, which sends `-1/2 ↦ -1/2` and `-1 ↦ -3/2 = δ_f^2(-1/2)`.
  Put `s_f = δ_f^(2k) s_0^- δ_f^(-k)` on `δ_f^k [-1, -1/2)`, which tiles `(-∞, x_0)`.
- *Gluing.* Put `s_f(x_0) = x_0` and `s_f(±∞) = ±∞`. Tiles near `x_0` go to tiles near `x_0`, so `s_f`
  is a homeomorphism of `[-∞, +∞]`.
- *Relation.* By construction, `s_f δ_f = δ_f^2 s_f` on every tile, and so everywhere.
- *Local form.* On each tile, `s_f` is a composition of finitely many dyadic affine maps with dyadic
  breakpoints. So `s_f` is dyadic PL with finitely many pieces near every point other than `x_0`, `+∞`
  and `-∞`.

**(d) The chain configuration and the singular orbits.**
- `s_f δ_f s_f^-1 = δ_f^2` and `δ_f σ δ_f^-1 = σ^2` hold exactly, and `σ = x+1` has infinite order. So
  `(s_f^-1, δ_f^-1, σ)` is a chain configuration in `Γ_f = ⟨V, δ_f, s_f⟩`, in the convention of
  `higman-chain-group-pbh-iff-chain-configuration`. This is exactly the pattern of `(a^-1, b^-1, c)` in
  `bs-chain-configurations-exist-in-finite-germ-extensions-of-v`.
- By the local-form argument of that node, the singular points are `±∞` for `δ_f`, and `x_0, ±∞`
  for `s_f`.
- In the Cantor coding, `x_0` lies in block `-1`, with fraction `5/6 = 0.11(01)^∞`. So it is a rational
  point with tail `(01)^∞`, in a `V`-orbit different from `O_0 ∋ -∞` and `O_1 ∋ +∞`. So there are
  three singular orbits.

**(e) Germ group at `x_0`.**
- `x_0` is not dyadic, so its Cantor germ is its two-sided real germ.
- *V-germs at `x_0`.* A `V`-germ there is dyadic affine, `x ↦ 2^k x + b`, with `b = x_0 (1 - 2^k)`
  dyadic, that is, `3 | 2^k - 1`, which holds iff `k` is even. So the `V`-isotropy is `⟨D_4⟩`, which is
  the germ of `δ_f`.
- *Generation.* The only singular germ in this orbit is `s̃ = [s_f]_(x_0)`. So the isotropy is
  `⟨D_4, s̃⟩`, with `s̃ D_4 s̃^-1 = D_4^2`. This is a quotient of `BS(1,2)` whose base has infinite order,
  hence `≅ BS(1,2)`, by the faithful-factor argument of the same node. It is finitely presented.
- *Non-triviality.* `s̃ ∉ ⟨D_4⟩`, because it conjugates `D_4` to `D_16`. So `x_0` is genuinely singular.

**(f) Germ groups at `±∞`.**
- At `+∞`: `Q_+ = ⟨σ, δ_f, s_f⟩`. This is exactly the germ group of the w16 computations.
- At `-∞`: `Q_- = ⟨σ, δ_f, s_f⟩` built from the left-side data.
- Both are quotients of `G_1`, since the relations hold globally. No other singular germ lies in their
  orbits.
- Finite presentation of `Q_-` is therefore needed as well. The faithful-germ route supplies it only if
  `θ_-` is faithful (P1-). The data on the two sides (`s_0` and `s_0^-`) are independent choices. ∎
