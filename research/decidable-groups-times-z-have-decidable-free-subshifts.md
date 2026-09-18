---
rg: 2
id: decidable-groups-times-z-have-decidable-free-subshifts
kind: claim
title: For every finitely generated group A with solvable word problem, A x Z carries a nonempty free subshift with decidable language, built from independent per-level colored nets stored along a Toeplitz column
distinct_from:
  decidable-groups-carry-free-subshifts-with-decidable-language: that is premise (D) for an arbitrary finitely presented decidable group, open; this proves (D) for every group of the form A x Z with A finitely generated and decidable, which is all the master route needs, since A x Z is again a finitely presented overgroup of the input when A is.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), with minimality; this gives no minimality. Minimality is then manufactured by the tree gluing of free-products-with-z-inherit-m2-from-decidable-free-subshifts.
  gjs-countable-groups-have-free-minimal-subflows: that gives free minimal subflows non-effectively; this gives a free subshift whose extension problem is decidable, with no minimality and no choice of a limit point.
---

**ESTABLISHED (lane proof, bh-g1-bss, 2026-09-18; elementary; unreviewed; no priority
claimed for the ingredients).**
- Covering nets with proper colorings as freeness witnesses are standard in Borel and
  continuous combinatorics (Kechris–Solecki–Todorcevic; Gao–Jackson–Seward).
- Toeplitz columns as storage are standard in symbolic dynamics.
- What is new here is only the observation that, once each level has its own rows, every
  constraint is greedily completable. That makes the extension problem decidable.

**Statement.** Let `A` be a finitely generated group with solvable word problem. Then
`Γ = A x Z` carries a nonempty subshift `Y ⊆ ({0,1}^2)^Γ` such that:
- `Γ` acts freely on `Y`;
- the set of finite patterns that extend to a point of `Y` is decidable.

**Conventions.**
- `Γ` acts by `(g·y)(x) = y(g^{-1}x)`.
- `|·|` is word length on `A` for a fixed finite generating set, and `d(a,b) = |a^{-1}b|` is
  the left-invariant metric.
- A set `M ⊆ A` is *`r`-separated* if distinct points are at distance at least `r`. It is
  *maximal* if every `a ∈ A` has `d(a, M) < r`.
- Balls `B(m)` are computable finite sets, by the word problem.

## Construction

**Parameters (computable).**
- `r_k = k + 1`.
- `E_k = 2r_k + k`.
- `P_k = |B(E_k)| + 1` colors, written with `J_k = ⌈log_2 P_k⌉` bits.
- Fix a computable bijection `ℓ ↔ (k, j)`, `0 ≤ j < J_k`, between the levels `ℓ ≥ 1` and the
  bit slots.

**Levels on `Z`.**
- For `ω ∈ Z_2` (2-adic integers) and `n ∈ Z`, the *level* is `lev_ω(n) = v_2(n − ω) + 1`,
  which is infinite for at most one `n`.
- The Toeplitz row is `T_ω(n) = lev_ω(n) mod 2` at finite levels, with either value at an
  infinite level.
- `X_T` is the set of all such rows. It is a closed, shift-invariant set of rows, all
  aperiodic.
- **Recognition lemma.** The row on `n + [−2^{ℓ+2}, 2^{ℓ+2}]` determines `ω mod 2^ℓ`, hence
  whether `lev(n) ≤ ℓ`, and if so its value.
  - *Proof, by induction on `j`.* Given `ω mod 2^j`, the coset `ω + 2^jZ` splits into two
    halves.
  - On `ω + 2^j + 2^{j+1}Z` the row is constant (`= j+1 mod 2`).
  - On `ω + 2^{j+1}Z` it takes both values (levels `j+2` and `j+3` occur), within any window
    of length `2^{j+3}`. ∎

**The subshift `Y`.** Points are pairs of layers:
- a *ruler* `R : Γ -> {0,1}`;
- a *data* layer `D : Γ -> {0,1}`.

Write `lev(n)` for the level read from the ruler row. The rules:
1. **Ruler.** `R(a,n)` does not depend on `a`, and the common row lies in `X_T`.
2. **Constancy.** If `lev(n) = ℓ` is finite, then `D(a,n) = D(a, n + 2^ℓ)` for all `a`. So the
   rows of level `ℓ` carry one field `f_ℓ : A -> {0,1}`.
3. **Level `k`.** Let `M_k = { a : f_{ℓ(k,0)}(a) = 1 }`, and let `col_k(a) ∈ {0,1}^{J_k}` be read
   from `f_{ℓ(k,j)}(a)`. Then:
   - `M_k` is a maximal `r_k`-separated set;
   - `col_k(a) ≠ col_k(b)` whenever `a ≠ b ∈ M_k` and `d(a,b) ≤ E_k`.

All rules are local:
- rule 1 has radius 1 along `A` plus the windows of `X_T`;
- rule 2 has radius `2^{ℓ+2}` along `Z`;
- rule 3 has radius `E_k` along `A` and `2^{L_k+2}` along `Z`, where `L_k = max_j ℓ(k,j)`.

The forbidden patterns are enumerable, uniformly in `k` and `ℓ`, so `Y` is effectively closed.

## Proof

**Nonempty.**
- Choose `ω` with no infinite level.
- For each `k`, a greedy scan of `A` in shortlex order gives a maximal `r_k`-separated `M_k`.
- A greedy coloring gives `col_k`: each point of `M_k` has fewer than `P_k` other points of
  `M_k` in its `E_k`-ball.
- Write the bits into the rows of the corresponding levels.

**Free.** Suppose `(s,n)·y = y`.
- **`n = 0`.** The ruler rows are `A`-constant, so the ruler row is `n`-periodic. Rows of
  `X_T` are aperiodic, so `n = 0`.
- **`s = 1`.** Suppose `s ≠ 1`, and put `k = |s|`. The data fields are invariant, so
  `M_k = sM_k` and `col_k(sa) = col_k(a)`.
  - By maximality some `c ∈ M_k` has `|c| < r_k`.
  - Then `sc ∈ M_k`, `sc ≠ c`, and `d(c,sc) = |c^{-1}sc| ≤ 2|c| + |s| < E_k`, with equal
    colors.
  - This contradicts rule 3. ∎

**Decidable language.** It suffices to decide patterns `p` on windows
`W = B(m) x [−N, N]`, since every finite pattern extends to such a window by a finite search.
Let `2^K ≤ 2N+1 < 2^{K+1}`.

*Step 1: ruler.*
- `p`'s ruler must be `A`-constant, and its row must agree on `[−N,N]` with some `T_ω`.
- Only finitely many cases arise: the classes `ω mod 2^{K+2}`, together with the value at the
  one possible position of higher level. So consistency is decidable.
- For each consistent class, every window position of level `≤ K+2` has a determined level.
- The positions of level `≥ K+3` lie in one coset of spacing `2^{K+2} > 2N+1`, so there is at
  most one such position `n*`. Its level can be made any `ℓ* ≥ K+3`, or infinite, by
  choosing the higher bits of `ω`; Step 2 uses the infinite choice.

*Step 2: revealed data.* For a consistent class:
- constancy (rule 2) is checked inside `W`;
- the window then reveals, for each level `ℓ ≤ K+2` occurring in it, the field `f_ℓ` on
  `B(m)`, plus the row at `n*`.
- Only finitely many `k` have a revealed slot.

If `n*` exists, take `ω = n*`. This is in the class, and `n*` then has infinite level. By the
definition of `X_T` its ruler value is free, and rules 2 and 3 never apply to its row. So the
row at `n*` imposes nothing. If `n*` does not exist, take any `ω` in the class.

*Step 3: each level separately.* Levels never interact. Fix `k` with a revealed slot. The
revealed data are:
- possibly the marker bits on `B(m)`;
- some of the color bits on `B(m)`.

**Claim.** `p` extends at level `k` iff the following finite search succeeds. There is a set
`N ⊆ B(m + r_k)` such that:
- (a) `N ∩ B(m)` agrees with the revealed marker bits, if they are revealed;
- (b) `N` is `r_k`-separated, and every point of `B(m)` is within distance `< r_k` of `N`;
- (c) there is an assignment of color strings to `N` that agrees with the revealed color bits
  at the points of `N ∩ B(m)` and is proper for the `E_k`-graph.

*Proof of the claim.*
- **Necessity.** Restrict a global solution to `B(m + r_k)`.
- **Sufficiency, markers.** Start from `N`, then scan `A \ (B(m) ∪ N)` greedily in shortlex
  order, adding each point at distance `≥ r_k` from all markers present. The union `M` is
  `r_k`-separated.
  - Points of `B(m)` are covered by `N`, by (b).
  - Every other point is in `N`, was added, or was skipped because a marker was nearer than
    `r_k`.
  - So `M` is maximal. The scan adds nothing inside `B(m)`, so `M ∩ B(m) = N ∩ B(m)`.
- **Sufficiency, colors.** Color the new markers greedily. Each has fewer than `P_k` colored
  neighbours. Non-marker sites of `B(m)` keep their revealed color bits, which no rule
  constrains.

*Conclusion.* `p ∈ L(Y)` iff, for some consistent ruler class, constancy holds in `W` and the
Step 3 search succeeds for each of the finitely many `k` with a revealed slot.
- The other levels are filled greedily, as in the nonemptiness proof.
- The row at `n*`, if any, is handled by Step 2.
- All searches are finite, so `L(Y)` is decidable. ∎

## Why this works where earlier attempts stopped

- **Independent levels.** The column over each `a ∈ A` stores unboundedly many bits, one
  Toeplitz level per bit. So the levels never share cells, and every per-level constraint
  (maximal net, proper coloring with a spare color) is greedily completable. The extension
  problem has computable look-ahead `r_k`, as asked in
  `decidable-groups-carry-free-subshifts-with-decidable-language`.
- **Freeness costs nothing.** The conjugator issue of Attempt 2 on (M2) disappears. The
  witnessing marker is chosen near the identity, and the coloring radius `E_k = 2r_k + k`
  absorbs the conjugation.
- **Minimality is not attempted.** It is supplied downstream by the tree gluing.

## Lesson for general BH

Decidability of an extension problem comes from *independence of scales*, not from
cleverness at any one scale.
- A single `Z` factor gives each point of the input group an unbounded private column.
- Then each scale's aperiodicity witness (a covering net with a proper coloring) is a
  flexible, greedily completable constraint on its own rows.
- So the "effectivity core" of gate E1, a free subshift with decidable language, holds for
  `A x Z` for every decidable `A`, and is no longer open on the route.

## Referee (bh-ref-e1-a, 2026-09-18): PASS

**Scope.** The whole node, with the Step 3 finite search and its greedy completion checked
line by line.

**Checked.**
- **Ruler.**
  - The level-`ℓ` positions form a coset of `2^ℓ Z`.
  - `X_T` (the rows `T_ω`, with a free value at the one infinite position) is closed: take a
    limit of `ω_i` in `Z_2`. It is also shift-invariant.
  - The recognition induction is correct. At stage `j` the half `ω + 2^j + 2^{j+1}Z` is
    constant. The half `ω + 2^{j+1}Z` contains positions of levels `j+2` and `j+3`, which
    have opposite parities, inside any `2^{j+3}` consecutive integers.
  - The infinite position always lies in the non-constant half, so its free value never
    misleads the recognition.
  - Aperiodicity follows, since a shift by `p` sends `T_ω` to `T_{ω+p}`.
- **Freeness.**
  - `n = 0` by aperiodicity.
  - Then `M_k = sM_k`. Some `c ∈ M_k` has `|c| < r_k`, and
    `d(c, sc) ≤ 2|c| + |s| ≤ 2r_k − 2 + k < E_k`, with equal colours. This contradicts rule 3.
  - The rules are invariant under the left action because `d` is left-invariant.
  - The argument also covers points with an infinite-level row, since every finite level
    occurs for every `ω`.
- **Step 1.** A window of length `2N+1 < 2^{K+2}` holds at most one position of level
  `≥ K+3`. Its level is free through the higher bits of `ω`, and `ω = n*` makes its row
  unconstrained.
- **Step 2.** Only levels `≤ K+2` are revealed. Each level belongs to exactly one `k`,
  through the bijection `ℓ ↔ (k,j)`.
- **Step 3 (the requested check): the claim holds.**
  - *Necessity.* `N = M_k ∩ B(m + r_k)` satisfies (a)–(c). The covering marker of any
    `a ∈ B(m)` lies in `B(m + r_k − 1)`.
  - *Sufficiency, markers.* The shortlex scan of `A ∖ (B(m) ∪ N)` tests against all markers
    present, so it keeps `r_k`-separation. Maximality holds case by case:
    - `B(m)` is covered by (b);
    - points of `N` and added points are markers;
    - a skipped point had a marker within `< r_k` when it was skipped.

    So `M ∩ B(m) = N ∩ B(m)`. The look-ahead is exactly the one annulus
    `B(m + r_k) ∖ B(m)`, and `p` does not constrain markers there.
  - *Sufficiency, colours.* New markers lie outside `B(m)`, so no revealed bit constrains
    them. Each has at most `|B(E_k)| − 1 < P_k ≤ 2^{J_k}` marker neighbours, so the greedy
    choice always succeeds. Properness on `N` is (c).
  - *Levels are independent*, and the unrevealed ones are filled as in the nonemptiness
    proof.
  - The reduction of an arbitrary finite pattern to a window `B(m) x [−N, N]` is the
    standard finite search.

**Nit.** The bijection `ℓ ↔ (k,j)` should range over `k ≥ 1`, since freeness uses
`k = |s| ≥ 1`. A level `k = 0` would be harmless.

**Scope of the result.** This is premise (D) for `A x Z`. There is no minimality; that is
supplied downstream. I searched no literature for a prior statement of exactly this.

**Credit.** Freeness through covering nets with proper colourings is the
Kechris–Solecki–Todorcevic / Gao–Jackson–Seward technique. Toeplitz storage is standard in
symbolic dynamics. The observation that separate rows make every level greedily completable,
and hence the language decidable, is this node's.
