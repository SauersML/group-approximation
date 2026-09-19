---
rg: 2
id: thick-building-flat-sfts-never-quantum-rigid-proof
kind: route
title: Exchange the half-apartment beyond each wall of a thick slab independently; unique lifting in the quotient keeps the two changes visible
target: thick-building-flat-sfts-are-never-quantum-rigid
requires: [sft-crossed-product-fp-iff-quantum-rigid, fp-crossed-products-force-connected-differences, fp-v-times-subshift-full-groups-force-quantum-rigidity]
---

Notation is as in the target. The proof is a lane proof and has not been reviewed.

**Recalled building facts, not re-read** (Abramenko–Brown, *Buildings*, Ch. 4, 5 and 11):
- (F1) For apartments `A, A'` there is a type-preserving isomorphism `A -> A'` fixing `A ∩ A'`
  pointwise.
- (F2) Complete apartment system. For a root `α` of an apartment `A`, a panel `π ⊆ ∂α` and a chamber
  `c ∉ α` containing `π`, the set `α ∪ {c}` lies in an apartment. This is the isometry criterion: a set
  of chambers W-isometric to a subset of `W` lies in an apartment.

For products of trees both facts are elementary. Flats are products of geodesic lines, and (F2) says a
geodesic ray can be continued through any of the at least two unused edges at its end vertex.

## Step 1. Unique lifting through the quotient

Let `d_1 ≠ d_2` be chambers sharing a panel `π`, and suppose `γ d_1 = d_2` with `γ ∈ Γ`.
- `γ` is type-preserving, so it maps `π`, the panel of `d_1` of its type, to the panel of `d_2` of that
  type. That panel is `π` itself.
- So `γ` fixes a simplex, and `γ = 1`, a contradiction.

So `p` is injective on the chambers through any panel. Induction along galleries then gives: if charts
`φ, ψ` agree at one chamber of a gallery-connected region `R ⊆ Σ` and `p∘φ = p∘ψ` on `R`, then
`φ = ψ` on `R`.

## Step 2. Two independent exchanges

- **The slab.** Fix a chart `φ : Σ -> A`, a wall `H` of `Σ`, and the parallel wall `H'` at distance
  `>= R + 2 diam(F)`. Write `Σ = Σ_- ∪ S ∪ Σ_+`, where `S` is the closed slab between the walls and
  `Σ_±` are the closed half-spaces beyond `H'` and `H`.
- **The roots.** `α = φ(Σ_- ∪ S)` is a root of `A` with boundary wall `φ(H')`, and `α' = φ(S ∪ Σ_+)` is
  a root with boundary wall `φ(H)`.
- **Exchange above `H'`.** Pick a panel `τ ⊆ H'` and put `π = φ(τ)`. Exactly two chambers of `A`
  contain `π`, and thickness gives a third, `c ∉ A`. By (F2) there is an apartment `A_1 ⊇ α ∪ {c}`.
- **Exchange below `H`.** Symmetrically there is `A_2 ⊇ α' ∪ {c'}`, with `c' ∉ A` containing
  `φ(τ')` for a panel `τ' ⊆ H`.
- **The charts.** By (F1) there are isomorphisms `ρ_i : A -> A_i` fixing `A ∩ A_i`. Put `φ_i = ρ_i ∘ φ`.
  Then `φ_1 = φ` on `Σ_- ∪ S`, and `φ_2 = φ` on `S ∪ Σ_+`.

## Step 3. The configurations

Put `x = x_(φ_1)` and `y = x_(φ_2)`.

- **Agreement on the slab.** Both `φ_i` equal `φ` on `S`. So `x(n) = y(n)` whenever `n + F ⊆ S`.
- **Difference beyond `H'`.**
  - Let `σ ⊆ Σ_+` be the chamber across `τ`.
  - In `A_1` the two chambers through `π` are the one in `α` and `c`, so `φ_1(σ) = c`.
  - Also `φ_2(σ) = φ(σ) ∈ A`, while `c ∉ A`, so `φ_1(σ) ≠ φ_2(σ)`.
  - Step 1 on `R = S ∪ {σ}` (where `φ_1 = φ_2` on `S`) gives `p∘φ_1(σ) ≠ p∘φ_2(σ)`.
  - So `x(n) ≠ y(n)` for the `n` with `σ ∈ n + F`, and that `n` is beyond `H'` up to `diam(F)`.
- **Difference beyond `H`.** The same argument with `σ'` across `τ'` gives a difference at a point
  beyond `H` up to `diam(F)`.

The two difference points lie on opposite sides of the lattice slab `M = {n : n + F ⊆ S}`. Their
distance is at least `R`.

## Step 4. Consequences

1. **Not quantum rigid.** Take `R > 2D + 2 diam(F)`. Split `L` as `I ⊔ M ⊔ O`, where `I` and `O` are
   the lattice points not in `M` on the two sides, so `d(I, O) > 2D`. `x` and `y` agree on `M` and
   differ in both `I` and `O`.
   - The certificate family on `W = k^2` of the route `positive-entropy-sft-crossed-products-are-not-fp-proof`
     (item 1) is diagonal in one basis on `I ∪ M` and in another on `M ∪ O`.
   - It checks (Q3) ball by ball, each ball against a single valid configuration, so only two points
     of the subshift are needed, over any `Z^d`.
   - It does not commute, so `X_Γ` is not `D`-quantum rigid.
2. **Not finitely presented.** `Δ(x, y)` meets both `I` and `O`. Since `R` is arbitrary, it is not
   `m`-connected for any fixed `m`. Part 1 of `fp-crossed-products-force-connected-differences` then
   says `LC(Y, k) ⋊ Z^d` has no presentation with relators of bounded length, for every subshift `Y`
   containing these pairs.
3. **Free subshifts.** For free `Y`, part 1 of `fp-v-times-subshift-full-groups-force-quantum-rigidity`
   gives the full-group statement by contraposition.

## Scope

- **Torsion.** Torsion-freeness is used only in Step 1. With torsion, Step 1 needs the chosen panels
  to have trivial stabilizer, which can be arranged when `Γ` acts freely on some `Γ`-orbit of panels.
  That case is not treated here.
- **Other codings.** Nothing is claimed about one-sided sector codings, which are finitely presented,
  or about the coding by `Γ` itself (`euclidean-building-boundary-shifts-are-quantum-rigid`).
