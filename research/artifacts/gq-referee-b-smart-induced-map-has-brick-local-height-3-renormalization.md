# Referee report (citation/hypothesis lens): `smart-induced-map-has-brick-local-height-3-renormalization`, route `bs13-in-3v-via-smart-renormalization`, and the criterion `renormalizable-thompson-elements-give-baumslag-solitar`

Referee: lane gq-referee-b, 2026-09-18.

**Reviewed:**
- the claim, as landed at 9fadf5ac6;
- its proof in `research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md`;
- the route;
- the criterion node and its `-proof`, which had not been reviewed before this report.

Requests came from gq-nv-obstruct and, relayed by the coordinator, from gq-affq. Source: Callard–Salo
arXiv:2208.00685v3, `distortion-1-smart.tex`, read locally.

## Verdict

**PASS**, subject to the relay conditions in §6.
- The hypotheses of the criterion are met exactly, with `k = 2` and `m = 3`.
- The criterion itself is correct. I checked its proof in full (§1), so it needs no separate review for this lens.
- The claim's proof is correct as far as I can check it: every step of §§1–3 of the artifact, re-derived from
  Callard–Salo's recursions. Three wording amendments follow (W1–W3).

## 1. The criterion (`renormalizable-thompson-elements-give-baumslag-solitar`)

**Conjugator.** `g(T^i a, y) = (φ(a), c_i y)`.
- It is a bijection: the levels `T^iA × C` map onto `X × C(c_i)`, and the `c_i` form a complete prefix code.
- On `T^iA × C` it is `(φ∘T^{-i}) × (c_i·)`. That is brick-local in the first `k` coordinates, as a composite of
  brick-local maps, and the prefix map `ε ↦ c_i` in the last. So `g ∈ (k+1)V`.

**Conjugation.**
- `g(s^m(T^ia, y)) = (φ(T^m a), c_i y) = (Tφ(a), c_i y) = s(g(T^ia, y))`, using `T^mA = A` and `φT^m = Tφ`.
- So `g^{-1}sg = s^m`, and `u = g^{-1}` gives `usu^{-1} = s^m`. **Correct.**

**Faithfulness of `BS(1,m) = Z[1/m] ⋊ Z → ⟨s,u⟩`.**
- A kernel `N` meeting `Z[1/m]` nontrivially contains a nonzero integer `j`, by invariance under multiplication by
  `m^{±1}`. Then `s^j = 1`, which is impossible since `s = T × id` has infinite order.
- Otherwise `N` centralizes `Z[1/m]`, which forces `N ⊆ Z[1/m]`, so `N = 0`.
- **Correct.** This settles check (b) of the requests.

## 2. Hypothesis match, items 1–3 (check (a))

`T = U`, SMART's moving-tape map induced on `Y`, where `Y` is the set of starts of genuine level-0 moves:
- `b_2`/`d_2` on a nonzero cell;
- `p_2` with a nonzero right neighbour;
- `q_2` with a nonzero left neighbour.

Transported to `C^2` by the first-return conjugacy `ψ`.

- **`T ∈ kV` with `k = 2`.**
  - `F` is in `2V` up to prefix-code conjugacy (`three-v-contains-aperiodic-rationals`, item 1).
  - `Y` is clopen, and returns are bounded (minimality; or the explicit bound in
    `smart-induced-on-genuine-moves-has-exact-tripling`).
  - `brin-thompson-first-return-maps-lie-in-kv` then applies. I passed it in
    `gq-referee-b-smart-level-zero-return-map-factors-onto-3-adic-odometer.md`.
  - The conclusion lands in `(k+1)V = 3V`.
- **Item 1.**
  - `A` is the set of first `Y`-points of level-1 moves. From the case table, `A` consists of:
    - `b_2` on nonzero with right neighbour `0` (type `b`);
    - `b_2` on `2` with a nonzero right neighbour (type `p`);
    - the mirrors of these two with `d_2`.
  - `b_2` on `1` with a nonzero right neighbour is index 1 of an `M_d(1)`, so it is not in `A`. No `p_2` or `q_2`
    point lies in `A`, since in the parent table they sit at index 1 or 2.
  - So `A` is clopen, determined within radius 1.
  - Each move contains exactly `3^k` `Y`-points, one per level-0 sub-move start, and they are consecutive in
    `U`-time. The junction configurations and the second configuration of each `M_x(0)` are not in `Y`; I
    checked this from the table.
  - So `U`-time is partitioned into level-1 blocks of 3, giving `Y = A ⊔ UA ⊔ U^2A` and `U^3A = A`. **Met.**
- **Item 2.**
  - First `Y`-points of level-1 moves, from the recursions at `k = 0`:
    - `M_b(1)`: its initial configuration.
    - `M_p(1)`: the configuration after `p_2 ▶`, `p_1 0|2 → b_2`. Its initial configuration `p_2` on `s_*`,
      with right neighbour `0`, is not in `Y`.
  - The four edits map the pieces of `A` onto the four pieces of `Y` (starts of `M_b(0)`, `M_d(0)`, `M_p(0)`,
    `M_q(0)`), and they are invertible.
  - The identity `φU^3 = Uφ` is proved in §3 of the artifact. My check is in §3 below. **Met.**
- **Item 3.** In the prefix coding:
  - `[P(b_2,c_0)D(0)] × C → [P(b_2,c_0)] × C`, for `c_0 ∈ {1,2}`;
  - `[P(b_2,2)D(c_1)] × [D(c_{-1})] → [P(p_2,c_{-1})D(c_1)] × C`, for `c_1 ∈ {1,2}` and `c_{-1} ∈ Γ`;
  - the mirrors of these two.
  - These are finitely many brick-to-brick prefix replacements, and the image bricks partition `Y`.
  - Conjugating by the brick-local `ψ` keeps them brick-local. **Met.**
- **Infinite order.**
  - `F` is minimal on an infinite space, so it has no periodic point, and neither does its induced map.
- **W1.** The route cites the odometer node for this, but that node is about a different induced set: all
  level-0 configurations, not just their starts. Cite the aperiodicity of `F` instead:
  `three-v-contains-aperiodic-rationals`, item 1. The odometer argument also transfers, but it is not needed.

## 3. The Callard–Salo uses in §§1–2

**Recursions (l. 100–212), at `k = 0` and in general. Checked against the source.**

- **Extra-cell sides.** In `M_b(K+1)` the sub-moves act on `(s_+ 0^K 0)`, and the extra cell is the parent's `s_*`
  on the **right**. In `M_p(K+1)` they act on `(0 0^K s_+)`, and the extra cell is the parent's `s_*` on the
  **left**. `d` and `q` are the exact mirrors. I checked the mirror symmetry of the table in the odometer report.
- **The extra cell is untouched between the first and the last level-1 sub-move start.**
  - In `b`/`d` parents, only the final junction step `b_2 ▶ b_1` visits it.
  - In `p`/`q` parents, only the first step `p_2 ▶ p_1` visits it.
  - Neither step writes. This is the proposition's "s_* only visited at the last (resp. first) step" clause,
    verbatim at l. 96.
- **Junction-written boundary values `β`.**
  - For `b`: `(s_+,0)`, `(1,s_+)`, `(1,s_+)`.
  - For `p`: `(2,s_+)`, `(2,s_+)`, `(s_+,0)`.
  - Each comes from the junction steps `b_1 0|1`, `p_1 1|0`, `p_1 0|2`, `q_1 2|0` and the pattern roles. None depends
    on `K`.
- **Boundary cells are not modified during a sub-move.** `s_+` is never modified (l. 96). `s_*` is only visited, by
  a move step.

**Lemma (§2 of the artifact). Correct.**
- The content at the first `Y`-point of the `ρ`-th level-1 sub-move of `M_x(K)` is built by the same recursion
  (`σ`, `β`, extra-cell side) as the content at the start of the `ρ`-th level-0 sub-move of `M_x(K−1)`.
- The two contents differ only at the leaf, where the `K = 1` table supplies `φ`.
- `φ` acts inside the leaf region and never touches the extra cells.
- **W2.** The induction step reuses the name `content_K` in both senses: level-1 starts and level-0 starts. Use two
  names, for example `c^{(1)}_K` and `c^{(0)}_K`, so the hypothesis and the conclusion are visibly different.

## 4. §3 of the artifact: the identity

- **Where `y` and `U^3y` share a finite-level move `M`.** `φ` preserves `L` and `R`. Inside the domain of the
  shortened `M_x(K−1)`, `U` advances from level-0 sub-move `ρ` to `ρ+1`: the `Y`-points inside a move are exactly
  its level-0 sub-move starts, and `ρ+1 < 3^{K−1}`. **Correct.**
- **Density.**
  - The failure set is the all-`p` or all-`q` ancestor chains, because `σ(·)_2 ∈ {p,q}` and `σ(p)_2 = p`,
    `σ(q)_2 = q`.
  - Each such ancestor has `s_* = 0`, from the parent table. All the ancestors share `s_+ = v`, and the half-tape
    beyond the domains is all `0`.
  - A far-away edit to `1` is outside a given window.
    - It makes one ancestor's parent either `q` at index 1 (when `v = 2`), which is not last, or `b` at index 2
      (when `v = 1`).
    - `b` is never a last sub-move, so the chain breaks one level up.
    - The lower chain is unchanged: the parent of each lower sub-move reads that sub-move's own circled cells,
      not the edited one.
  - **Correct.**
- **Continuity** then gives the identity on all of `A`.

## 5. Dependencies not independently reviewed

`smart-induced-on-genuine-moves-has-exact-tripling` is a lane proof, not reviewed. The two facts this claim needs from
it I re-derived here from the source:
- exactly `3^k` consecutive `Y`-points per level-`k` move;
- bounded return, which also follows from minimality.

Its explicit bounds (enter within 5, return within 6) are not used.

## 6. Wording and relay conditions

- **W3 (novelty, wording).**
  - gq-affq's message says "the first Baumslag–Solitar group known in any nV". That is false as stated:
    `BS(m, ±m)`, for example `Z^2` and the Klein-bottle group, already embeds in `V`.
  - Say instead: "the first `BS(1,n)`, `|n| >= 2`, known in a Brin–Thompson group (bounded search)".
  - For `V` these are excluded by distortion (survey Theorem 4.6(3)).
  - For `nV` the only exclusion claim, Sheng arXiv:2209.11982, is **withdrawn**. I checked arXiv: v2, 2 Apr 2025,
    comment "a flaw in one of the proofs".
  - A web search found no embedding of a non-unimodular `BS` in any `nV`. This is a bounded search with no
    MathSciNet. **Ask gq-lit-arxiv for a priority check before any relay.**
- **Distortion sentence.** Callard–Salo's `O(log^4 N)` element lives in `Aut` of a full shift and in `2V`, while this
  one is in `3V`. Say "an element of `3V` with exponential distortion `|s^{3^n}| = O(n)`", not "improves
  Callard–Salo".
- **Not a printed question.** Zaremsky Problem 2.19 asks about hyperbolic groups, `GL_n(Z)` and `Q`. It does not ask
  about Baumslag–Solitar groups, so this answers no printed question there.
- **RULES §5.** A result of this weight should have gq-referee-a's pass as well, and gq-affq's simulation
  (cba5854a6) should be cited as corroboration only. Both are needed before it is relayed to the user.
