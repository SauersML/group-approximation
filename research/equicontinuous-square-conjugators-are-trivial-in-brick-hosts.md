---
rg: 2
id: equicontinuous-square-conjugators-are-trivial-in-brick-hosts
kind: claim
title: In a group of brick maps of C^n with isometric sections, equicontinuity is the same as bounded exponent sums, and an element conjugated to an even power of itself by an equicontinuous homeomorphism has finite order, so the odometer of 2V_tau renormalizes nothing and every BS(1,2) conjugator there has unbounded exponent sums
distinct_from:
  bg-in-isometric-brick-hosts-needs-unbounded-exponents: that shows the base a of a Baumslag--Gersten image has unbounded exponent sums, using the stable letter; this concerns the conjugator of any BS(1,2), needs no stable letter, and adds the converse (equicontinuity forces bounded sums).
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that proves, in one dimension, that the base of a proper-power relation is equicontinuous; this is in every dimension, is about the conjugator, and shows that equicontinuous conjugators of even powers are trivial.
  baumslag-gersten-splits-over-bs12-edges: that isolates the height-two tower K as the input of the stable-permutation route; this excludes the odometer as the middle element a_1 of any copy of K in these hosts.
---

**ESTABLISHED** (lane proof, elementary; no novelty claimed). Reviewed: gq-referee-a PASS
(`research/artifacts/gq-referee-a-equicontinuous-square-conjugators-are-trivial-in-brick-hosts.md`,
9d96cb601; nits N1–N3 applied).

## Setting

As in `bg-in-isometric-brick-hosts-needs-unbounded-exponents`:
- `𝔅_n` is the group of brick maps of `C^n` with isometric sections (tuples of automorphisms of the
  binary rooted tree);
- `L(g)` is the table length, `δ_g` the exponent cocycle, and `S_m(x) = δ_(g^m)(x)`;
- the metric is `d(x,y) = 2^(-m(x,y))`.

`𝔅_n` contains `nV`, `2V_τ` and the affine `2V` hosts. A family of maps is *equicontinuous* in
the usual sense.

## Statement

Let `g ∈ 𝔅_n`.
1. **Equicontinuity = bounded sums.** `{g^m : m ∈ Z}` is equicontinuous iff
   `sup_(m,x) |S_m(x)|_∞ < ∞`.
2. **Pro-2 powers.** If so, some `g^J` with `J ≥ 1` maps every brick `B_q` of some level `N`
   onto itself as `q w ↦ q η_q(w)`, with `η_q` a tuple of tree automorphisms. So `cl⟨g^J⟩`
   (uniform topology) is pro-2.
3. **Even powers.** Let `f` be any homeomorphism of `C^n` with `{f^m}` equicontinuous, and suppose
   `f g f^-1 = g^k` with `k` even and nonzero. Then `g` has finite order.

## Consequences

- **The odometer renormalizes nothing.** In `2V_τ` the element `s = τ × id` is an isometry. So
  `s g s^-1 = g^2` forces `g` to have finite order. In the height-two tower
  `K = ⟨a_0, a_1, a_2⟩` of `baumslag-gersten-splits-over-bs12-edges`, the middle element `a_1`
  cannot be `s`, nor any other equicontinuous element.
- **Conjugators.** If `⟨g, f⟩ ≅ BS(1,2)` inside `𝔅_n`, then by item 3 `f` is not equicontinuous,
  and by item 1 it has unbounded exponent sums. The base `g` may be equicontinuous, as
  `s ∈ 2V_τ` is.
- **Parity is needed.** `M_3(x) = 3x` on `C = Z_2` is an isometry, and `M_3 τ M_3^-1 = τ^3`. So an
  equicontinuous element of `𝔅_1` conjugates the odometer to its cube. In item 3, `k` odd is
  genuinely different.

## Proof

**Item 1, ⇐.** This is item 2 of the proof of
`bg-in-isometric-brick-hosts-needs-unbounded-exponents`, which uses only the bound on sums.

**Item 1, ⇒.**
- *Setup.* Let `L = L(g) = L(g^-1)`. Equicontinuity gives `N_1` such that `d(x,y) ≤ 2^(-N_1)`
  implies `d(g^m x, g^m y) ≤ 2^(-(L+1))` for all `m`.
- *Choose a record time.* Suppose `S^j_n(x) ≤ −(N_1 + L)` for some `n ≥ 1`, `x`, `j`. Let
  `E' = −min_(0≤i≤n) S^j_i(x) ≥ N_1 + L`, and let `m*` be the first `i` with `S^j_i(x) = −E'`.
  Then `m* ≥ 1`.
- *Bound the reading length.* The reading-length recursion of that proof,
  `ℓ^j_(i+1) ≤ max(ℓ^j_i, L − S^j_i)` with `ℓ^j_0 = 0`, gives `ℓ := ℓ^j_(m*)(x) ≤ L + E' − 1`,
  because `−S^j_i(x) ≤ E' − 1` for `i < m*`. Here `ℓ` may be any length at least the least reading
  length, and the recursion bound is such a length. On its reading brick, `g^(m*)` acts by one prefix
  replacement with an isometric section. The coordinate-`j` image prefix has length
  `ℓ − E' ≥ 0`. So `E' ≤ ℓ ≤ L + E' − 1`.
- *Contradiction.* Let `y` equal `x` except in coordinate `j`, where it agrees with `x_j` on exactly
  `ℓ` digits. Then `d(x,y) = 2^(-ℓ) ≤ 2^(-N_1)`. A tree automorphism preserves the level of first
  difference, so `g^(m*) x` and `g^(m*) y` first differ in coordinate `j` at depth `ℓ − E' ≤ L − 1`.
  Hence `d(g^(m*) x, g^(m*) y) ≥ 2^(-(L−1)) > 2^(-(L+1))`, a contradiction.
- *Both directions.* So `S^j ≥ −(N_1 + L)` for positive times. Positive times of `g^-1` give the
  other bound, because the family `{g^-m}` is the same and `S_m(g^-1, y) = −S_m(g, g^-m y)`.

**Item 2.**
- *Bounded reading lengths.* By item 1 and the recursion, reading lengths are bounded by some
  `L + K` for all `m ∈ Z` (use `g^-1` for `m < 0`). Put `N = L + K`. Every `g^m` acts on every
  level-`N` brick `B_q` by one replacement `q ↦ v^(m)(q)`, with a section and
  `|v^(m)_j| ∈ [N − K, N + K]`.
- *Pigeonhole.* The type `q ↦ v^(m)(q)` takes finitely many values, so two times `m_1 < m_2` share
  it.
- *The power.* `g^(m_1)` maps `B_q` bijectively onto `C(v)` by one section, so `g^(-m_1)` maps
  `C(v)` back onto `B_q` by the inverse section. Then `g^J = g^(-m_1) g^(m_2)`, with
  `J = m_2 − m_1`, maps `B_q` onto itself as `q w ↦ q η_q(w)`, and so do all its powers.
- *Pro-2.* The group of all such maps is `∏_q Aut(T_2)^n`. It is compact, closed in the uniform
  topology, and pro-2, since `Aut(T_2)` is an iterated wreath product of `Z/2`. So `cl⟨g^J⟩` is
  pro-2.

**Item 3.**
- *A return time.* `{f^m}` and `{f^-m}` are equicontinuous, so by Arzelà–Ascoli `cl⟨f⟩` is a
  compact group of homeomorphisms in the uniform topology. In a compact monothetic group, `id` is a
  limit of `f^m` with `m → +∞`. So `f^(m_i) → id` uniformly along some `m_i → +∞`. Then `g^(k^(m_i)) = f^(m_i) g f^(-m_i) → g` uniformly, so
  `g^(M_i) → id` uniformly with `M_i = k^(m_i) − 1`, which is odd and nonzero.
- *The subgroups `P_N`.* Let `P_N = {m : g^m maps every level-N brick onto itself}`. This is the set
  of `m` with `g^m` uniformly `2^(-N)`-close to `id`, a subgroup `d_N Z`. It contains `M_i` for
  large `i`, so `d_N ≥ 1` is odd.
- *Equicontinuity.* Given `N`, pick `N' ≥ N` such that each `g^r`, `0 ≤ r < d_N`, maps level-`N'`
  bricks into level-`N` bricks. For `m = d_N q + r`, first `g^r` and then `g^(d_N q)`, which
  preserves level-`N` bricks, send points of one level-`N'` brick into one level-`N` brick. So
  `{g^m}` is equicontinuous.
- *Odd closure.* The uniform topology on `⟨g⟩` has neighbourhood basis `g^(P_N)`. So `cl⟨g⟩` is the
  completion `lim Z/d_N` (or finite). Its open subgroups of odd index form a basis, so it and all its
  closed subgroups are pro-odd.
- *Conclusion.* By item 2, `cl⟨g^J⟩` is a closed subgroup of `cl⟨g⟩`, hence pro-odd, and it is
  pro-2. So it is trivial, `g^J = id`, and `g` has finite order. `∎`

## Lesson for general BH

**Prime compatibility.** Suppose a relation `x ~ x^k` with `p | k` holds inside a compact
(equicontinuous) regime. Then it forces the closure of `⟨x⟩` to be `p`-free. Host local groups that
are pro-`p`, such as isometries of the binary tree, which are pro-2, can absorb only relations whose
powers are prime to `p`.

This gives a quick test for any candidate host of a proper-power input: compare the prime support
of the input's power relations with the pro-structure of the host's section groups. When they
collide, the conjugators must leave the compact regime. They must have unbounded exponent cocycles
or non-isometric local maps.

For `BS(1,m)` with `m` odd the test passes, which is why `BS(1,3)` fits naturally (the parity
example `M_3`). For `m = 2` it fails, which is why every `BS(1,2)`, tower or Baumslag--Gersten
design in these hosts needs expanding conjugators.
