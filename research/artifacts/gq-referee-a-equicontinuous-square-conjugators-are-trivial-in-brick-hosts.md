# Referee report (gq-referee-a, proof-gap lens): equicontinuous square conjugators are trivial in brick hosts

**Reviewed:** `equicontinuous-square-conjugators-are-trivial-in-brick-hosts` (lane bh-one-relator, 010df8cad), read on
origin/main. Its setting and reading-length recursion come from `bg-in-isometric-brick-hosts-needs-unbounded-exponents`,
which I refereed as PASS in 5d3e18e0b.

**Verdict: PASS.** There are three nits.
- For the citation lens: Arzelà–Ascoli.

## (1) Item 1, the direction ⇒: the record-time argument (the author asked about this)
- **The setup.**
  - `L(g) = L(g^(−1))`, because the inverse table has the same words.
  - `N_1` exists by uniform equicontinuity on a compact space.
- **The record time.** Let `m*` be the first time the running minimum `−E'` is attained.
  - `S_0 = 0 > −E'`, so `m* ≥ 1`.
  - `−S^j_i ≤ E' − 1` for `i < m*`.
  - So the recursion gives a valid reading length `ℓ ≤ max(0, L + E' − 1)`.
- **Bounds on `ℓ`.** The coordinate-`j` image prefix has length `ℓ + S^j_(m*) = ℓ − E'`. Since this is at least 0,
  `E' ≤ ℓ`.
- **The witness `y`.**
  - `y` lies in the same reading brick, because only coordinate `j` changes, and it changes after position `ℓ`.
  - `d(x,y) = 2^(−ℓ) ≤ 2^(−N_1)`, since `ℓ ≥ E' ≥ N_1 + L`.
- **The contradiction.**
  - On that brick, `g^(m*)` is `u_jw ↦ v_jη(w)` with `|v_j| = ℓ − E' ≤ L − 1`.
  - A tree automorphism keeps the level of first difference.
  - The other coordinates stay equal, because brick maps act coordinatewise.
  - So `d(g^(m*)x, g^(m*)y) = 2^(−(ℓ−E')) ≥ 2^(−(L−1))`, which is the contradiction. ✓
- **The other direction.** It comes from `S_n(g^(−1), y) = −S_n(g, g^(−n)y)`, applied to the equicontinuous family
  `{g^(−m)}`. Negative times are `S_n(g^(−1), ·)`. ✓

## (2) Item 2: pigeonhole and pro-2 (the author asked about this)
- **Level-`N` bricks.** With `N = L + K`, every `g^m` acts on every level-`N` brick by one replacement with
  `|v_j| = N + S^j_m ∈ [N−K, N+K]`.
- **Pigeonhole.** There are finitely many level-`N` bricks and finitely many possible image words, so finitely many
  types. Two times `m_1 < m_2` share a type.
- **The power `g^J`.** `g^(−m_1)` inverts `g^(m_1)` on `C(v)`, so `g^J` maps each `B_q` to itself by `qw ↦ qη_q(w)`.
  Such maps form the compact group `∏_q Aut(T_2)^n`, which is closed in the uniform topology and pro-2. So
  `cl⟨g^J⟩` is pro-2. ✓

## (3) Item 3: from return times to a trivial pro-2 subgroup (the author asked about this)
- **The return time.**
  - `{f^m : m ∈ Z}` is equicontinuous and closed under inverses, so `cl⟨f⟩` is a compact group of homeomorphisms.
  - Differences of a convergent subsequence give `f^(m_i) → id` with `m_i → ∞`.
  - Conjugation is continuous, so `g^(k^(m_i)) → g`.
  - `M_i = k^(m_i) − 1` is odd, because `k` is even, and nonzero, because `|k| ≥ 2`. This holds for negative `k` too.
    ✓
- **The subgroups `P_N`.** `g^m` being `2^(−N)`-close to the identity is the same as preserving every level-`N`
  brick, since finitely many bricks are each mapped into themselves. So `P_N = d_NZ`, with `d_N ≥ 1` odd, because it
  divides some `M_i`. ✓
- **Equicontinuity.** Write `m = d_Nq + r`. Then `g^r` maps each level-`N'` brick into a level-`N` brick, and
  `g^(d_Nq)` preserves those. ✓
- **Pro-odd.**
  - The subgroups `cl(g^(d_NZ))` are open of odd index `d_N` and form a basis at the identity. So `cl⟨g⟩` is pro-odd
    (or finite of odd order).
  - A closed subgroup that is both pro-odd and pro-2 is trivial. So `g^J = id`. ✓
  - Item 2 applies because `g ∈ 𝔅_n`, and item 1 turns its equicontinuity into bounded sums.

## (4) The parity example (the author asked about this)
- `M_3(x) = 3x` is an isometry of `Z_2`, since 3 is a unit, hence a tree automorphism. So `M_3 ∈ 𝔅_1` with the trivial
  table and section `M_3`.
- `M_3τM_3^(−1)(x) = 3(x/3 + 1) = x + 3 = τ³(x)`.
- So item 3 genuinely needs `k` even. ✓

## The consequences
- `s = τ × id` is an isometry. So `sgs^(−1) = g²` forces finite order.
- In a faithful copy of `K`, `a_0` has infinite order. So `a_1` is not equicontinuous, and by item 1 its exponent
  sums are unbounded.
- The base `s` of `⟨s,u⟩` can be equicontinuous, and `u` is not.
- All of these follow. ✓

## Nits
- **N1 (item 1, ⇒).** Say that `ℓ` is the recursion bound, not the least reading length. A brick map restricts to a
  brick map on every sub-brick, so any length above the least one works. Say also that `y` lies in that reading brick.
- **N2 (item 3).** Add the two standard lines:
  - `cl⟨f⟩` is a compact group of homeomorphisms, because the family is equicontinuous together with its inverses;
  - `id` is a limit of `f^m` with `m → +∞`, by taking differences along a convergent subsequence.
- **N3 (item 3, "Odd closure").** State the conclusion as: the subgroups `cl(g^(d_NZ))` are open of odd index and form
  a neighbourhood basis. That is what makes every closed subgroup, and in particular `cl⟨g^J⟩`, pro-odd.
