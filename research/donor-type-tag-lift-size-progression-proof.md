---
rg: 2
id: donor-type-tag-lift-size-progression-proof
kind: route
title: Split each active symbol into t phases carried along donors, then solve z + bt = 2^j
target: donor-covering-types-give-nonsurjunctive-size-progressions
requires:
  - ec-groups-share-the-nonsurjunctive-alphabet-sizes
artifacts:
  - experiments/donor-power-residue-2026-09-17/check.py
---

Notation as in the target. The prerequisite is used only for the definition of `NS(G)` and `NS_all`. Items 4 and 5
are implications involving open claims (`some-nonsurjunctive-group-gives-a-binary-power-one`,
`every-group-is-surjunctive-over-binary-power-alphabets`); they are proved as implications and use neither claim as
a premise of the route.

**Import, verbatim** (`ec-groups-share-the-nonsurjunctive-alphabet-sizes`): "For a group `K`, let `NS(K)` be the set
of integers `n >= 2` such that some injective, non-surjective cellular automaton on `A^K` exists with `|A| = n`. Let
`NS_all` be the union of `NS(G)` over all groups `G`."

**Item 1.** Fix `t >= 1`. Let `C = Z ⊔ (B × Z/t)` and `σ: C → L` with `σ(z) = z` on `Z` and `σ(β, s) = β`. For
`c = (β, s)` put `φ(c) = s`. Let `Z/t` act on `C` by fixing `Z` and by `r·(β, s) = (β, s + r)`.
- *Rule.* For `v ∈ C^M` let `u = σ∘v ∈ L^M`. Put `Ψ(v) = μ(u)` if `μ(u) ∈ Z`, and `Ψ(v) = (μ(u), φ(v(d(u))))` if
  `μ(u) ∈ B`. This is well defined: if `μ(u) ∈ B`, (D1) for `ℓ` with `ℓ|_M = u` at the site `1` gives
  `u(d(u)) ∈ B`, so `v(d(u)) ∈ B × Z/t`. Let `Φ(y)(g) = Ψ((g^(-1)y)|_M)`, a cellular automaton with memory `M`.
- *Labels.* `σ(Ψ(v)) = μ(σ∘v)`, hence `σ∘Φ = τ∘σ` sitewise. With `ℓ = σ∘y`: if `τ(ℓ)(g) ∈ B` then
  `Φ(y)(g) = (τ(ℓ)(g), φ(y(D_ℓ(g))))`.
- *Injective.* Let `Φ(y) = Φ(y')`. Then `τ(σ∘y) = σ∘Φ(y) = σ∘Φ(y') = τ(σ∘y')`, so `σ∘y = σ∘y' =: ℓ`, since `τ` is
  injective, and `D_ℓ` is the same for `y` and `y'`. Let `h ∈ G`. If `ℓ(h) ∈ Z` then `y(h) = ℓ(h) = y'(h)`. If
  `ℓ(h) ∈ B`, (D2) gives `g` with `τ(ℓ)(g) ∈ B` and `D_ℓ(g) = h`. Reading second coordinates of
  `Φ(y)(g) = Φ(y')(g)` gives `φ(y(h)) = φ(y'(h))`. Together with `σ(y(h)) = σ(y'(h))` this is `y(h) = y'(h)`.
- *Not surjective.* `σ: C^G → L^G` is onto (send `ℓ` to `y` with `y(h) = ℓ(h)` on rest sites and `(ℓ(h), 0)` on
  active sites). If `Φ` were onto, `τ∘σ = σ∘Φ` would be onto, so `τ` would be onto. It is not.
- *Donor-covering.* Split `C = Z ⊔ (B × Z/t)`. `Ψ(v)` is active iff `μ(σ∘v) ∈ B`; put `d'(v) = d(σ∘v)`, so
  `D'_y = D_(σ∘y)`. (D1) for `Φ`: an active output at `g` has `ℓ(D_ℓ(g)) ∈ B`, so `y(D'_y(g))` is active. (D2) for
  `Φ`: `y(h)` active means `ℓ(h) ∈ B`, and the relay `g` for `ℓ` is a relay for `y`.
- So `Φ` is strict and donor-covering of type `(z, bt)` over the alphabet `C` of size `z + bt >= z + b = |L| >= 2` (a one-point shift carries no strict automaton). Hence
  `z + bt ∈ NS(G)` by the definition imported above. (This is item 2 of `donor-covering-phase-transport-proof`, with
  the proof written out so that nothing depends on that open route.)

**Item 2.** For `n > z` take `t = n - z >= 1` in item 1.

**Item 3.** Write `b = 2^v b'`, `b'` odd, and `z'' = z / 2^v` when `2^v | z`.
- (⇐) Let `z'' ≡ 2^(i_0) (mod b')` and let `o` be the order of `2` modulo `b'` (`o = 1` if `b' = 1`). For
  `i = i_0 + o s` with `s` large, `2^i > z''` and `b' | 2^i - z''`. Then `2^(i+v) - z = 2^v (2^i - z'')` is positive
  and divisible by `2^v b' = b`, so `t = (2^(i+v) - z) / b >= 1` and `z + bt = 2^(i+v)`.
- (⇒) Let `z + bt = 2^j` with `t >= 1`.
  - If `z = 0` then `b t = 2^j`, so `b' = 1`, and the condition holds trivially.
  - Let `z > 0` and `u = v_2(z)`. Suppose `u < v`. Since `v_2(bt) >= v > u`, `v_2(z + bt) = u`, so `2^j = 2^u <= z`.
    But `z + bt > z`, a contradiction. So `u >= v` and `2^v | z`.
  - `2^j = z + bt >= b >= 2^v`, so `j >= v`. Dividing by `2^v`: `z'' + b' t = 2^(j-v)`, i.e.
    `z'' ≡ 2^(j-v) (mod b')`.
- `gcd(z, b)` divides `z + bt = 2^j`, so it is a power of two.
- Examples. `(z, 1)`: `b' = 1`, `v = 0`. `(1, b)`, `b` odd: `z'' = 1 = 2^0`. `(2, b)`, `4 ∤ b`: `v <= 1`, `2^v | 2`,
  and `z'' ∈ {1, 2}`. `b` an odd prime with `2` a primitive root and `b ∤ z`: `⟨2⟩ = (Z/b)^×` contains `z mod b`.
  For `(3, 5)`: `3 + 5 = 8`. For `(5, 3)`: `5 + 3 = 8`. For `(2, 11)`: `2 + 11·186 = 2048`.

**Item 4.**
- (⇐) Let `NS_all ≠ ∅`. By hypothesis some group `G` carries a strict donor-covering automaton of power-residue type
  `(z, b)`, so `z + bt = 2^j` for some `t >= 1`, and item 1 gives `2^j ∈ NS(G) ⊆ NS_all`. Here `j >= 1` because
  `z + bt >= 2`.
- (⇒) Let `NS_all ≠ ∅`. The claim gives `2^j ∈ NS(H)` for some group `H` and `j >= 1`: a strict `β` on `A^H`,
  `|A| = 2^j`, with rule `ν` and memory `M ∋ 1`. Put `L = A × {r, a}`, `Z = A × {r}`, `B = A × {a}`, and
  `τ(a, s) = (β(a), s)`, with rule `μ(u) = (ν(first coordinates of u), second coordinate of u(1))`.
  - `τ` is injective because `β` is and the second layer is copied. It is not surjective: its first layer misses what
    `β` misses.
  - `μ(u) ∈ B` iff `u(1) ∈ B`. Take `d ≡ 1`. (D1): an active output at `g` has `ℓ(g) ∈ B`. (D2): an active input
    at `h` is relayed by `g = h`.
  - The type is `(2^j, 2^j)`, and `2^j + 2^j·1 = 2^(j+1)`, so it is power-residue.

**Item 5.** Let `G` carry an injective, non-surjective donor-covering automaton of power-residue type `(z, b)`, with
`z + bt = 2^j`. Item 1 gives `2^j ∈ NS(G)`, contradicting the assumed surjunctivity of `G` at the alphabet size `2^j`. A single active symbol
is type `(z, 1)`, which is power-residue by item 3.
