---
rg: 2
id: retract-segment-steps-perfect-kernel-one-relator-proof
kind: route
title: A map from a segment to Z taking the value 1 on one edge element retracts the segment onto that edge group, so the retract-tree lemma climbs the cyclic Magnus step, while the lower central weights of a perfect-kernel segment force every interior letter into every residually nilpotent kernel
target: retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h
requires:
  - vertex-injective-quotients-give-hughes-free-division-rings
  - magnus-segment-steps-put-one-relator-groups-in-h
---

## Inputs

- **(C)** `𝓗` is closed under subgroups, extensions and directed unions, and contains free groups. Groups in `𝓗`
  are locally indicable, hence torsion-free. This is item 1 of
  [[vertex-injective-quotients-give-hughes-free-division-rings]].
- **(R)** Retract trees, item 6 there: if `B ∈ 𝓗` retracts onto `A` or onto `C = θ(A)`, then the HNN extension
  `B *_θ` is in `𝓗`.
- **(M)** Magnus–Moldavanskii, as recorded in [[magnus-segment-steps-put-one-relator-groups-in-h-proof]]:
  - `W_n = <a_{n+1}, …, a_{n+m}>` is free of rank `m` in `S_[0,n]` (Freiheitssatz);
  - `S_[0,n+1] = S_[0,n] *_{W_n} B_{n+1}` with `B_{n+1} = <a_{n+1}, …, a_{n+1+m} | r'_{n+1}>`;
  - `N = ker(G -> Z)` is the directed union of the `S_[p,n]`, and `S_[p,n] ≅ S_[0,n-p]` by the shift.
- **(T)** The twist, from item 1 of the same route: the substitution `a_{n+m} ↦ α_n^{-1} σ β_n^{-1}` is an
  automorphism of `F(a_n, …, a_{n+m})` fixing `W_{n-1}` pointwise. So if it turns `r'` into the cyclic word
  `σ^{-1} x σ y`, then `S_[0,n] = S_[0,n-1] *_{x_n ↦ y_n^{-1}}`, the HNN extension with stable letter `σ` and
  `σ^{-1} x_n σ = y_n^{-1}`, where `x_n, y_n ∈ W_{n-1}` are the shifts of `x, y` by `n`.
  - The edge groups `<x_n>` and `<y_n>` are infinite cyclic, since `x, y` are nontrivial in the free group
    `F(a_0, …, a_{m-1})` and `W_{n-1}` is free on the shifted letters.
  - If the substitution gives `σ x σ^{-1} y` instead, rotate to `σ^{-1} y σ x`. This swaps `x` and `y`, and the
    hypothesis of item 1 is symmetric in them.

## The integral window lattice

A homomorphism `S_[0,n] -> Z` is an integer vector `(z_0, …, z_{n+m})` with `Σ_{i=0}^m e_i z_{j+i} = 0` for
`0 ≤ j ≤ n`. Let `Λ_{n+1} ⊆ Z^m` be the set of its top windows `(z_{n+1}, …, z_{n+m})`, and `Λ_0 = Z^m`, the top
windows of `S_[0,-1]`, which is free.

- **Recursion.** Restricting a solution for `j ≤ n` to `j ≤ n - 1` gives a window `(z_n, …, z_{n+m-1}) ∈ Λ_n`.
  Conversely, a solution for `j ≤ n - 1` with that window extends by any integer `z_{n+m}` with
  `Σ_i e_i z_{n+i} = 0`. So `Λ_{n+1}` is the set of `(w_1, …, w_m)` with `(w_0, …, w_{m-1}) ∈ Λ_n` and
  `e · w = 0` for some `w_0`, which is the definition in the claim.
- **Monotone chain.** Call this map `Φ`. It is monotone and `Λ_1 ⊆ Λ_0`, so `Λ_{n+1} ⊆ Λ_n` for all `n`. If
  `Λ_{N+1} = Λ_N` then `Λ_{N+2} = Φ(Λ_{N+1}) = Φ(Λ_N) = Λ_{N+1}`, so the chain is constant from `N` on.
  - Unlike the rational chain it need not stabilize. For `e = (2, -3)` it is `2^n Z`, and the certifier then
    declines.
- **Values.** For `v ∈ W_{n-1}` with exponent vector `c_v` in `a_n, …, a_{n+m-1}`, the values of the maps
  `S_[0,n-1] -> Z` on `v` are `{c_v · w : w ∈ Λ_n}`. This is the subgroup `gZ` with `g` the gcd of the values
  on a basis of `Λ_n`. So some `ψ` has `ψ(v) = 1` iff `g = 1`.

## Item 1: the retract segment step

Take the top case; the bottom case is the top case for `t^{-1}`, which reverses the indices. By (M) and (C) it
is enough to show `S_[0,n] ∈ 𝓗` for all `n ≥ -1`. Then `N ∈ 𝓗` as a directed union of copies of these, and
`G = N ⋊ Z ∈ 𝓗`.

Induction on `n`. `S_[0,-1]` is free. Let `n ≥ 0` and `S = S_[0,n-1] ∈ 𝓗`. By (T),
`S_[0,n] = S *_θ` with `θ: <x_n> -> <y_n>`, `x_n ↦ y_n^{-1}`.
- Suppose `c_x` takes the value `1` on `Λ_n`. By the window lattice, some `ψ: S -> Z` has `ψ(x_n) = 1`. Define
  `ρ: S -> <x_n>`, `ρ(g) = x_n^{ψ(g)}`. It is a homomorphism because `<x_n>` is abelian, and `ρ(x_n) = x_n`. So
  `ρ` is a retraction of `S` onto the edge group `A = <x_n>`.
- If instead `c_y` takes the value `1`, then `ρ(g) = y_n^{ψ(g)}` with `ψ(y_n) = 1` retracts `S` onto
  `C = θ(A) = <y_n>`.
- Either way (R) gives `S_[0,n] ∈ 𝓗`.

No map to `Z` has to see the other edge element, and none is asked to be injective on a larger group: `ψ` is
only used to build a retraction. ∎

**Where the hypotheses are used.** `x ≠ 1` and `y ≠ 1` make the edge groups infinite cyclic, so (T) is an HNN
extension over `Z`. The value `1`, not just a nonzero value, is what makes `ρ` the identity on the edge group.
With `ψ(x_n) = d > 1`, `ρ(x_n) = x_n^d` and there is no retraction. Rule 1 of the segment-step node needed
only `d ≠ 0`, but for both edge elements.

## Item 2: the perfect-kernel family

Let `e = (0, ε, 0)` with `ε = ±1`.
- **Lattices.** `Λ_1` is the set of `(w_1, w_2)` with `ε w_1 = 0`, so `Λ_1 = {(0, w)}`. `Φ(Λ_1)` is the set of
  `(w_1, w_2)` with `w_0 = 0` and `ε w_1 = 0`, which is again `Λ_1`. So `Λ_0 = Z^2` and `Λ_n = {(0, w)}` for
  `n ≥ 1`. In homology: the relations of `S_[0,n]` in `H_1` are `ε z_{j+1} = 0` for `0 ≤ j ≤ n`, so
  `H_1(S_[0,n]) = Z a_0 ⊕ Z a_{n+2}`.
- **The test.** For `c = (c_0, c_1)`, the gcd of the values on `Λ_n` is `gcd(c_0, c_1)` for `n = 0` and `|c_1|` for
  `n ≥ 1`. If `|c_1| = 1`, both are `1`. So the hypothesis of item 1 holds for every `n` as soon as the
  `a_1`-exponent of `x` or of `y` is `±1`.
- **The words.** If `a_2` occurs exactly twice in `r'`, with opposite signs, then `α = β = 1` gives
  `r' = a_2^{-1} x a_2 y` cyclically with `x, y ∈ F(a_0, a_1)`. They are nontrivial: if `x = 1` then `r' = y`
  has no `a_2`, and if `y = 1` then `r' = a_2^{-1} x a_2` is not cyclically reduced.
  - A twist by `α, β` replaces `x, y` by conjugates, so `c_x, c_y` do not depend on it, and `c_x + c_y = (e_0, e_1)
    = (0, ε)`.
  - Hence `c_1(x) + c_1(y) = ε`, and if one of them is `0` the other is `ε = ±1`. ∎

## Item 3: weights, and no bounded-length target

Fix `e = (0, ε, 0)` and write `r' = R(a_0, a_1, a_2)`, so `r'_j = R(a_j, a_{j+1}, a_{j+2})`. For a group `Q`
and `u ∈ Q`, let `wt(u) = sup{k : u ∈ γ_k(Q)} ∈ {1, 2, …, ∞}`.

**Weight lemma.** If `u_0, u_1, u_2 ∈ Q` satisfy `R(u_0, u_1, u_2) = 1`, then `wt(u_1) ≥ wt(u_0) + wt(u_2)`.
- In `F(x_0, x_1, x_2)`, write `R = R(x_0, 1, x_2) · c` with `c ∈ <<x_1>>`. Then `c` is a product of conjugates
  `g x_1^{δ} g^{-1}` with `Σ δ = ε`, the `x_1`-exponent of `R`, since `R(x_0, 1, x_2)` has no `x_1`.
- `R(x_0, 1, x_2) ∈ F(x_0, x_2)` has exponent sums `e_0 = e_2 = 0`, so it lies in `[F(x_0, x_2), F(x_0, x_2)]`, the
  normal closure of `[x_0, x_2]`. So `R(u_0, 1, u_2) ∈ γ_{wt(u_0) + wt(u_2)}(Q)`.
- For `u ∈ γ_w(Q)` and `g ∈ Q`, `u^{-1} g u g^{-1}` is a commutator of an element of `γ_w(Q)` with one of `Q`,
  so `g u g^{-1} ∈ u γ_{w+1}(Q)`. As `γ_{w+1}(Q)` is normal and `γ_w/γ_{w+1}` is central in `Q/γ_{w+1}`, the
  product of conjugates satisfies `c(u) ∈ u_1^ε γ_{wt(u_1)+1}(Q)` (when `wt(u_1) = ∞` there is nothing to prove).
- So `u_1^ε ∈ γ_k(Q)` with `k = min(wt(u_0) + wt(u_2), wt(u_1) + 1)`. If `wt(u_1) < wt(u_0) + wt(u_2)`, then
  `u_1 ∈ γ_{wt(u_1)+1}`, which contradicts the definition unless `wt(u_1) = ∞`. ∎

**Two consecutive relations.** If `r'_j` and `r'_{j+1}` hold for the images `u_i` of `a_i`, then
`w_{j+1} ≥ w_j + w_{j+2}` and `w_{j+2} ≥ w_{j+1} + w_{j+3}`. So `w_{j+1} ≥ w_j + w_{j+1} + w_{j+3} ≥ w_{j+1} + 2`,
and `w_{j+1} = ∞`, and then `w_{j+2} = ∞`.

**Residually nilpotent targets.** For `n ≥ 1` the pairs `(r'_j, r'_{j+1})`, `0 ≤ j ≤ n - 1`, give
`wt(φ(a_i)) = ∞` for `1 ≤ i ≤ n + 1` and every `φ: S_[0,n] -> Q`. If `Q` is residually nilpotent,
`γ_ω(Q) = 1` and `φ` kills `a_1, …, a_{n+1}`.
- Killing `a_1, …, a_{n+1}` turns `r'_0` into `R(a_0, 1, 1)`, `r'_n` into `R(1, 1, a_{n+2})` and the others
  into `1`. The first two are trivial because `e_0 = e_2 = 0`. So `S_[0,n] / <<a_1, …, a_{n+1}>> = F(a_0, a_{n+2})`.
- This quotient is free, hence residually nilpotent, so it is the largest residually nilpotent quotient. And
  `a_1 ≠ 1` in `S_[0,n]`, since `S_[0,-1] = F(a_0, a_1)` embeds in `S_[0,n]` by (M), so `S_[0,n]` is not
  residually nilpotent.

**Length-`k` targets.** Let `Y_k` be the class of groups with a subnormal series
`1 = P_0 ⊴ P_1 ⊴ … ⊴ P_k = Q` with residually nilpotent factors. Claim: for `n ≥ 2k - 1`, every
`φ: S_[0,n] -> Q ∈ Y_k` kills `a_j` for `k ≤ j ≤ n + 2 - k`.
- `k = 1` is the previous paragraph.
- For `k ≥ 2`, put `P = P_{k-1}`. The composite `S_[0,n] -> Q/P` kills `a_1, …, a_{n+1}`, so `φ` maps them into
  `P ∈ Y_{k-1}`. The generators `a_1, …, a_{n+1}` satisfy `r'_1, …, r'_{n-1}`, so `φ` restricts to a
  homomorphism from `S_[1,n-1] ≅ S_[0,n-2]` into `P`. Since `n - 2 ≥ 2(k-1) - 1`, induction kills the letters of
  indices `k - 1, …, n - k + 1` of `S_[0,n-2]`. Shifted by `1`, these are `a_k, …, a_{n+2-k}`. ∎

**Cascade for the survivors.** `survivor_structure.py` checks for each of the 12 survivors that `R(1, a_1, a_2)`
and `R(a_0, a_1, 1)` are conjugate to `a_1^{±1}`.
- So in `S_[0,n]`, `a_{j+1} ∈ <<a_j>>` (from `r'_j`, `j ≤ n`) and `a_{j-1} ∈ <<a_j>>` (from `r'_{j-2}`,
  `j ≥ 2`).
- Killing one interior letter `a_j`, `1 ≤ j ≤ n + 1`, therefore kills `a_1, …, a_{n+1}`.

**Consequence for item 5 of the segment-step node.** Let `φ: S_[0,n] -> Q` and `τ ∈ Q` satisfy that node's exact
criterion for the untwisted step `S_[0,n+1] = S_[0,n] *_{x_{n+1} ↦ y_{n+1}^{-1}}`.
- `φ` and `σ ↦ τ` define a map `S_[0,n+1] -> Q`.
- If `Q ∈ Y_k` with `n + 1 ≥ 2k - 1`, that is `k ≤ (n+2)/2`, the length-`k` claim and the cascade make it kill
  `a_1, …, a_{n+2}`, in particular `a_{n+1}`. This includes free groups, RAAGs and residually torsion-free
  nilpotent groups, all in `Y_1`.
- For each survivor one of `x, y` has `a_1`-exponent `0` (item 2). Its shift lies in `W_n = F(a_{n+1}, a_{n+2})`
  with `a_{n+2}`-exponent `0`, so in `<<a_{n+1}>>`, and `φ` kills it.
- If that element is `x_{n+1}`, `φ` is not injective on `<x_{n+1}>`. If it is `y_{n+1}`, then
  `φ(x_{n+1}) = τ φ(y_{n+1})^{-1} τ^{-1} = 1`, and again `φ` is not injective.

So no `Q_n` in these classes meets the criterion, and no one class `Y_k` serves every `n`. Item 1 goes around
this: at step `n` its target is the fundamental group of the retract tree, built from `S_[0,n]` itself. ∎

## Item 4: the computation

Run it from `experiments/perfect-kernel-segment-targets-2026-09-17/`. The scripts import the landed
`experiments/one-relator-hughes-free-char-p-2026-09-17/segment_certify.py` (hierarchy rules plus rule 1)
unchanged.
- `python3 retract_segment_certify.py > survivors.txt` prints a lattice calibration, then certifies the 12
  survivors and the 8 relators of length 11 that were open before rule 1.
  - Calibration: `e = (0,1,0)` gives the chain `Z^2 ⊋ {(0,w)}`, and `e = (2,-3)` does not stabilize.
  - Each survivor is certified as `nielsen(root-tower)` with step `top:retract-hnn(al=1,be=1,stab=1)`: one Nielsen
    normalization, then item 1 from the top with no twist.
- `python3 retract_segment_certify.py census 13 > census-L13.txt` runs the full census, single-threaded, in
  about 10 minutes. Rows `11 False True 2`, `12 False True 10` and `13 False True 28` are the relators that only
  item 1 certifies, and the `uncertified:` list is empty. The counts of words up to length 12 agree with the
  census of the segment-step node, which checks the harness.
- `python3 survivor_structure.py` checks (E) span `2` and `e = (0, ±1, 0)`, the two cascade conjugacies, and the
  vanishing of the exponent sums of `R(a_0, 1, a_2)`, for the 12 survivors. As a calibration, it also checks that
  the six length-11 rewrites certified by rule 1 are not of this type.
- `python3 nielsen_search.py 4 22` records that, without item 1, no Nielsen image of a survivor (up to 4
  elementary moves, length at most 22) is certified.

**What the code decides.** `retract_hnn` substitutes `a_m = α^{-1} σ β^{-1}` for `α, β` of length at most 2,
keeps words with exactly two `σ`-letters of opposite signs and nontrivial `x, y`, and tests
`gcd(c_x · Λ) = 1` or `gcd(c_y · Λ) = 1` on every term of the chain. The chain comes from `lattice_chain`
(exact integer Hermite normal form, at most `STAB = 12` steps). Every certificate rests on item 1 and on the
landed rules.
