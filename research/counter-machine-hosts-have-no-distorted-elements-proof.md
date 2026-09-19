---
rg: 2
id: counter-machine-hosts-have-no-distorted-elements-proof
kind: route
title: Deep in the periodic tails a counter machine commutes with a lattice, the lattice quotient has lower rank, a sublinear element translates by a fixed lattice vector that sublinearity kills, and only a finite box remains
target: counter-machine-hosts-have-no-distorted-elements
requires:
  - brin-thompson-mv-contains-a-distortion-element
---

Notation as in the claim. Only Corollary 3 uses the requirement. Everything else is
self-contained.

## Step 0: normalizing a CM-action

Let `Γ = ⟨S⟩` act on `X = Z^N × E` through `CM(N, E)`, with `S = S^{-1}`. Finitely many maps are
involved, so we may fix the following data for all `s ∈ S`:
- one family of colourings `κ_1, …, κ_N`, eventually periodic with common constants `T` and `p`
  (take the product colouring, the largest `T` and the lcm of the periods);
- one radius `r`;
- maps `D_s, G_s` on radius-`r` windows with `s(z, e) = (z + D_s(ω), G_s(ω))`;
- a bound `K ≥ 1` with `|D_s| ≤ K` for all `s`.

For colourings `λ = (λ_i)`, a point `x = (z, e)` and `ρ ≥ 0`, the **`ρ`-window** is
`W^λ_ρ(x) = (e, (λ_i(z_i + u))_{i ≤ N, |u| ≤ ρ})`.

For any colourings `λ`, let `s^λ` be the self-map of `Z^N × E` given by the same formula
`s^λ(z, e) = (z + D_s(ω), G_s(ω))`, with `ω` now read from `λ`. For a word
`w = s_ℓ ⋯ s_1` in the free group `F(S)` put `w^λ = s_ℓ^λ ∘ ⋯ ∘ s_1^λ`.

**Lemma 1 (locality).** Let `w` have length `ℓ` and put `ρ = r + Kℓ`. Suppose
`W^λ_ρ(z, e) = W^μ_ρ(z', e)`. Then:
- `w^λ(z, e) − (z, e)` and `w^μ(z', e) − (z', e)` have the same `Z^N`-component;
- `w^λ(z, e)` and `w^μ(z', e)` have the same `E`-component.

*Proof.* Induction on `ℓ`. The case `ℓ = 0` is clear. Write `w = s w'`. By induction, `w'` moves both
points by the same vector `d` with `|d| ≤ K(ℓ − 1)`, and gives the same `E`-component `f`. The
radius-`r` windows at `(z + d, f)` and `(z' + d, f)` sit inside the radius-`ρ` windows at `z` and
`z'`, shifted by `d`, since `r + |d| ≤ ρ`. So they are equal, and `s` acts on both in the same way. ∎

**Lemma 2 (transfer to models).** Suppose that every window of `λ` occurs in `κ`: for every `ρ`
and `x'`, some `x` has `W^λ_ρ(x') = W^κ_ρ(x)`. Then `s ↦ s^λ` extends to an action of `Γ` on
`Z^N × E` by bijections. Every `γ ∈ Γ` moves every point by at most `K|γ|_S` in `Z^N`.

*Proof.* Let `w ∈ F(S)` be trivial in `Γ`. Then `w^κ = id`. Given `x'`, choose `x` with the same
radius-`(r + K|w|)` window. By Lemma 1, `w^λ` moves `x'` exactly as `w^κ` moves `x`, that is, not at
all. So `w^λ = id`. Applied to `s s^{-1}` and `s^{-1} s`, this shows each `s^λ` is a bijection. So
`w ↦ w^λ` factors through `Γ`. The displacement bound follows from `|D_s| ≤ K`. ∎

We call such a `λ`-action a **model** of the given action. The action in Lemma 2 is again a
CM-action whenever `λ` is eventually periodic.

## Step 1: induction on N

**Claim `P(N)`.** Let `N` be fixed. For every finite `E`, every finitely generated `Γ`, every
CM-action of `Γ` on `Z^N × E`, and every `g ∈ Γ` with `|g^n|_S = o(n)`, some `g^J` with `J ≥ 1`
acts as the identity.

**`P(0)`.** Here `X = E` is finite, so `g^{|E|!}` acts trivially.

**Step `P(< N) ⇒ P(N)`, for `N ≥ 1`.** Fix the data of Step 0.

*Tail colourings.* For each `i`, let `κ_i^+` and `κ_i^-` be the `p`-periodic colourings of `Z`
that agree with `κ_i` on `[T, ∞)` and on `(−∞, −T]` respectively. They exist because `κ_i` is
`p`-periodic on each of these half-lines.

*Models.* For a nonempty `B ⊆ {1, …, N}` and signs `σ ∈ {+, −}^B`, let `κ^{B,σ}` be the colouring
with `κ^{B,σ}_i = κ_i^{σ_i}` for `i ∈ B` and `κ^{B,σ}_i = κ_i` for `i ∉ B`.

Every window of `κ^{B,σ}` occurs in `κ`. Given `x' = (z', e)` and `ρ`, set `z_i = z'_i` for
`i ∉ B`. For `i ∈ B`, set `z_i = z'_i + p q_i`, with the integer `q_i` chosen so that
`σ_i z_i ≥ T + ρ`. For `i ∈ B` and `|u| ≤ ρ`, the point `z_i + u` lies in the tail half-line of
sign `σ_i`. So `κ_i(z_i + u) = κ_i^{σ_i}(z_i + u) = κ_i^{σ_i}(z'_i + u)`, by periodicity. So
`W^κ_ρ(z, e) = W^{κ^{B,σ}}_ρ(x')`.

By Lemma 2, `Γ` acts on `X^{B,σ} = Z^N × E` through the formulas read from `κ^{B,σ}`.

*The lattice.* Let `Λ_B ⊆ Z^N` be the vectors supported on `B` with all entries in `pZ`.
- `κ^{B,σ}` is invariant under translation by `Λ_B`. So each `s^{κ^{B,σ}}` commutes with every
  translation `τ_v`, `v ∈ Λ_B`, and so does all of `Γ`.
- The action descends to the quotient `X^{B,σ}/Λ_B ≅ Z^{B^c} × (E × (Z/p)^B)`.
- This quotient action is a CM-action of `Γ` of dimension `N − |B| < N`, with finite fibre
  `E' = E × (Z/p)^B`. The displacement in the `B^c`-coordinates and the new fibre value are read
  from three things: `e`, the residues `z_B mod p` (which determine every `κ_i^{σ_i}`-window for
  `i ∈ B`), and the `κ_i`-windows for `i ∉ B`. These colourings are eventually periodic. The new
  residues are `z_B + D_B mod p`.
- By `P(N − |B|)`, some `g^{j}` with `j = j_{B,σ} ≥ 1` acts trivially on the quotient.

*Lift.* Let `x' ∈ X^{B,σ}`.
- Since `g^j` is trivial on the quotient, `g^j x' = x' + λ(x')` with `λ(x') ∈ Λ_B`. The
  `B^c`-coordinates and the fibre are unchanged.
- `λ(x' + v) = λ(x')` for `v ∈ Λ_B`, because `g^j` commutes with `τ_v`.
- So `g^{jn} x' = x' + n λ(x')` for all `n ≥ 1`.
- Lemma 2 gives `n|λ(x')| ≤ K |g^{jn}|_S = o(n)`. So `λ(x') = 0`.

Hence `g^{j_{B,σ}}` acts trivially on every model `X^{B,σ}`.

*The finite box.*
- Let `J_0` be the lcm of the finitely many `j_{B,σ}`. Fix a word `w` of length `ℓ` representing
  `g^{J_0}`, and put `ρ = r + Kℓ`.
- For `x = (z, e) ∈ X`, let `B(x) = {i : |z_i| ≥ T + ρ}`.
- Suppose `B = B(x) ≠ ∅`. Let `σ_i` be the sign of `z_i` for `i ∈ B`. For `i ∈ B`, the window of
  radius `ρ` around `z_i` lies in the tail half-line where `κ_i = κ_i^{σ_i}`. So
  `W^κ_ρ(x) = W^{κ^{B,σ}}_ρ(x)`. By Lemma 1, `g^{J_0}` moves `x` in `X` exactly as it moves `x` in
  the model `X^{B,σ}`, that is, not at all.
- So `g^{J_0}` fixes every point outside `Q = (−T − ρ, T + ρ)^N × E`, which is finite. A bijection
  fixing the complement of `Q` permutes `Q`, so `g^{J_0 · |Q|!} = id`.

This proves `P(N)`. By induction, `P(N)` holds for every `N`, which is the **Theorem**. ∎

## Step 2: corollaries

**Corollary 1.** Apply the Theorem to the inclusion of a finitely generated `Γ ≤ CM(N, E)`. An
element of sublinear growth then has finite order, so it is not distorted.

**Corollary 2.** It suffices to show that each named group contains a distorted element, since a
subgroup of `CM(N, E)` that contains one contradicts Corollary 1.
- **`H = H_3(Z)`, with `c = [a, b]` central.** Then `[a^q, b^q] = c^{q^2}`. For `M ≥ 1` write
  `q = ⌊√M⌋` and `M = q^2 + t` with `0 ≤ t ≤ 2q`. So `|c^M| ≤ 4q + 4t ≤ 12q ≤ 12√M`. This is
  sublinear, and `c` has infinite order.
- **`BS(1, m) = ⟨a, t | t a t^{-1} = a^m⟩` with `|m| ≥ 2`.** Here `a^{m^k} = t^k a t^{-k}` has
  length at most `2k + 1`, and `a` has infinite order.
- **`SL_n(Z)` and `GL_n(Z)` for `n ≥ 3`.** The upper unitriangular `3 × 3` block gives a copy of
  `H_3(Z)`.

For the last sentence of Corollary 2: in a CM-action of `H_3(Z)`, the element `c` has sublinear
growth, so some `c^J` acts trivially.

**Corollary 3.** By `brin-thompson-mv-contains-a-distortion-element`, which imports Callard–Salo
(arXiv:2208.00685, Theorem E), `mV` contains a distorted element for `m ≥ 2`. Now apply Corollary 1.

**Corollary 4.** Consider a product-coloured realization in the sense of
`heisenberg-in-mv-reduces-to-zn-subshift-realization` (C), item 2.
- It is an action of `H_3(Z)` on `Z^N` with a free orbit.
- Each generator `s` moves `z` by `F_s(κ_1(z_1), …, κ_N(z_N))`.
- If every `κ_i` is eventually periodic, this is a CM-action with `E` a point and `r = 0`.
- By Corollary 2, some `c^J` with `J ≥ 1` acts trivially. So no orbit is free, which is a
  contradiction. ∎

## Remarks

- The proof uses only one property of `g`, namely `|g^n| = o(n)`. It uses neither centrality nor
  commutation. So it also kills every group in which some infinite-order element is distorted. This
  includes quotients of `BS(m, n)` that keep `[t a t^{-1}, a]`, by
  `bs-quotients-keeping-a-commutator-need-distortion` (OPEN, not used here).
- Why the method stops at eventually periodic tapes: the finite-box step needs finitely many tail
  models, one for each `(B, σ)`. For a Toeplitz or Sturmian tape, the tails realize infinitely many
  windows that no periodic model contains, and the induction has no base to fall back on.
