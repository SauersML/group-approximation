---
rg: 2
id: locally-moving-simple-subgroup-commutator-proof
kind: route
title: A double commutator with an element moving a small open set lands a nontrivial commutator of the simple subgroup inside any subgroup it normalizes
target: fp-groups-with-a-locally-moving-simple-subgroup-are-isolated
requires:
  - fp-simple-groups-are-isolated
---

Notation as in the target. `[a,b] = a b a^{-1} b^{-1}`. The node
`fp-simple-groups-are-isolated` is required only for the CGP definitions it quotes.

**Step 0. Disjointly supported elements commute.** Let `a, b` be bijections of `X` with
`a` fixing `X − U` pointwise and `b` fixing `X − W` pointwise, where `U ∩ W = ∅`.
- Since `a` is a bijection fixing `X − U` pointwise, `a(U) = U`; likewise `b(W) = W`.
- For `y ∈ U`: `b y = y` and `a y ∈ U`, so `b a y = a y = a b y`. The case `y ∈ W` is
  symmetric. For `y ∉ U ∪ W` both fix `y`.
So `ab = ba`.

**Step 1 (top). Item 1.** Let `1 ≠ n ∈ N`.
- By faithfulness pick `x` with `nx ≠ x`. By Hausdorffness pick disjoint open `A ∋ x`,
  `B ∋ nx`, and set `U = A ∩ n^{-1}B`. It is open, contains `x`, and `nU ⊆ B`, so
  `nU ∩ U = ∅`.
- `T_U` is nonabelian: pick `g, h ∈ T_U` with `[g,h] ≠ 1`.
- `[g,n] = (g n g^{-1}) n^{-1} ∈ N`, since `g ∈ T` normalizes `N`.
- Write `[g,n] = g k` with `k = n g^{-1} n^{-1}`. The element `k` fixes `X − nU`
  pointwise, and `h` fixes `X − U` pointwise, so `kh = hk` by Step 0.
- Hence `[[g,n],h] = g k h k^{-1} g^{-1} h^{-1} = g h g^{-1} h^{-1} = [g,h]`.
- Also `[[g,n],h] = [g,n] · (h [g,n]^{-1} h^{-1}) ∈ N`, since `h ∈ T` normalizes `N`.
So `1 ≠ [g,h] ∈ N ∩ T`. The subgroup `N ∩ T` is normalized by `T`, so it is a nontrivial
normal subgroup of the simple group `T`. Hence `T ≤ N`.

**Step 1 (fin). Item 1.** `Alt_fin(X)` is simple for `|X| ≥ 5`: for finite `X` this is
the simplicity of `A_m`, `m ≥ 5`, and for infinite `X` it is a directed union of such.
- Let `1 ≠ n ∈ N`, and pick `x` with `nx ≠ x`. Since `|X − {x, nx}| ≥ 3`, pick distinct
  `a, b ∉ {x, nx}` and set `g = (x a b) ∈ T`.
- `[g,n] = (g n g^{-1}) n^{-1} ∈ N`.
- `[g,n] = g · (n g^{-1} n^{-1})` is a product of two 3-cycles, so it lies in `T`.
- It is nontrivial: `n g n^{-1} = (nx na nb)` moves `nx`, and `g` does not. So
  `n g n^{-1} ≠ g`.
So `N ∩ T` is nontrivial and normal in `T`, and `T ≤ N`.

**Step 2. Item 2.** Let `1 ≠ c ∈ Γ`.
- (top): choose `x` and `U` as in Step 1 for `c`, and `1 ≠ t ∈ T_U`. Then `t` moves some
  `y ∈ U`. The element `c t c^{-1}` fixes `X − cU ∋ y`. So `c t c^{-1} ≠ t`.
- (fin): choose `x, g` as in Step 1 for `c`. Then `c g c^{-1} ≠ g`.
Either way `c ∉ C_Γ(T)`.

**Step 3. Item 3.** For `γ ∈ Γ`, `T^γ = γ T γ^{-1}` satisfies the same hypothesis.
- (top): `(T^γ)_U = γ T_{γ^{-1}U} γ^{-1}`, and `γ^{-1}U` is open.
- (fin): `T^γ = T`.

Let `1 ≠ K ⊴ M`. Every `T^γ ≤ M` normalizes `K`, so Step 1 applied to `T^γ` gives
`T^γ ≤ K`. Hence `M ≤ K`, and `M` is simple.

If `1 ≠ N ⊴ Γ`, then `T` normalizes `N`, so `T ≤ N` and `M ≤ N`. Finally
`C_Γ(M) ≤ C_Γ(T) = 1`, and conjugation embeds `Γ` in `Aut(M)`.

**Step 4. Items 4 and 5.** Pick `t ∈ T − {1}`. Every nontrivial normal subgroup contains
`T ∋ t`, so `F = {t}` is a finite discriminating subset. By CGP, Proposition, lines
554–557 (quoted in `fp-simple-groups-are-isolated`), a finitely presented, finitely
discriminable group is isolated.

**Examples (top).** For `V ≤ Γ ≤ Homeo(C)`, take `T = V`.
- A nonempty open `U` contains a cone `[w]`.
- The map `u ↦ wu` is a homeomorphism `C → [w]`. Transporting each `v ∈ V` along it and
  extending by the identity on `C − [w]` gives an element of `V`: it is piecewise prefix
  replacement on a partition consisting of cones inside `[w]` and the finitely many cones
  that make up `C − [w]`. This is an injective homomorphism `V → T_U`.
- So `T_U ⊇` a copy of `V`, which is nonabelian.
