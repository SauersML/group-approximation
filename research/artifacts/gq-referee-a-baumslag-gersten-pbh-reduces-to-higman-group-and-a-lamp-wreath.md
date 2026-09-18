# Referee report (gq-referee-a, proof-gap lens): Baumslag–Gersten PBH reduces to Higman's group and a lamp wreath

**Reviewed** (lane bh-one-relator, 175da33f5), read on origin/main:
- `baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath`, with the proof inline;
- the Attempts entry "Hierarchy-phase gauges" on `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`, which
  the author also asked about.

**Verdict: PASS.** The Attempt entry is correct as a dead-end record. There are three nits on the reduction and one
on the Attempt.
- The reduction is a conditional implication and is stated as one.
- Two of its inputs are unreviewed:
  - part 1 of `free-permutational-products-preserve-pbh`, a lane proof;
  - `baumslag-gersten-group-maps-onto-higman-groups`, by Reidemeister–Schreier.

## (1) `ρ`, and the Britton correspondence in all four sign cases (the author asked about this)
- **The splitting.** `BG = A *_φ`, with `A = ⟨a_0, a_1 | a_1a_0a_1^(−1) = a_0²⟩` and `φ : a_0 ↦ a_1`, since
  `ta_0t^(−1) = a_1` and the presentation is that of `BG`.
  - `A ↪ H_4` as `BS(1,2)` (Higman).
  - The identification of `A ≤ BG` with `⟨a_0, a_1⟩ ≤ H_4` is an isomorphism, since both are `BS(1,2)` on the same
    generators. ✓
- **`ρ` is well defined.** For `c ∈ C_1`, `(τu)c(τu)^(−1) = τcτ^(−1) = φ(c)`, because `u` centralizes `C_1`.
  `ρ(t)^(±1)` is `τu` or `u^(−1)τ^(−1)`.
- **The four sign cases.** Take a `BG`-reduced word `x_0t^(ε_1)x_1⋯`. The `Γ`-syllable between consecutive
  `u`-letters, and its pinch condition in `L`, are:

  | `(ε_i, ε_(i+1))` | pattern in `L` | pinch in `L` iff | pinch in `BG` iff |
  |---|---|---|---|
  | `(+,+)` | `u (x_iτ) u` | never | never |
  | `(+,−)` | `u x_i u^(−1)` | `x_i ∈ C_1` | `x_i ∈ C_1` |
  | `(−,+)` | `u^(−1)(τ^(−1)x_iτ)u` | `x_i ∈ τC_1τ^(−1) = C_2` | `x_i ∈ C_2` |
  | `(−,−)` | `u^(−1)(τ^(−1)x_i)u^(−1)` | never | never |

  The identity-edge HNN `L` has both associated subgroups equal to `C_1`, which is why the table has this form. So
  `BG`-reduced words map to `L`-reduced words with the same number `k ≥ 1` of stable letters, and Britton gives
  `ρ(g) ≠ 1`. The case `k = 0` is the inclusion `A ≤ Γ`. ✓

## (2) The necessity remark (the author asked about this)
- `⟨a, γ⟩` satisfies `(γaγ^(−1))a(γaγ^(−1))^(−1) = a²`, so it is a quotient of `BG`, and by hypothesis
  `⟨a, b⟩ ≅ BS(1,2)`.
- If `a_2 = γbγ^(−1)` lay in `⟨a_0, a_1⟩`, the `γ`-conjugate relation `a_2a_1a_2^(−1) = a_1²` would make `a_1`
  conjugate to `a_1²` inside `BS(1,2)`. The exponent homomorphism `a_0 ↦ 0`, `a_1 ↦ 1` gives `1 = 2`, a
  contradiction. ✓
- So `⟨a_0, a_1, a_2⟩` is a quotient of the tower `K` in which `B_0` survives and `a_2 ∉ B_0`, as the node says.

## (3) The infinite-edge clause, and the decidability caveat (the author asked about this)
- **The clause.** The cited node states part 1 for free permutational products. The step to the amalgam uses the
  standard isomorphism `W *_C (C × K) ≅ (*_(x ∈ W/C) K_x) ⋊ W = K *_(W/C) W`.
  - This holds for every `C`, finite or infinite: the normal closure of `K` is the free product of the conjugates
    `K^w`, one per coset `wC`, because `C` centralizes `K`.
  - With `W = Γ`, `C = ⟨a_0⟩` and `K = Z`, part 1 gives `L ∈ B_A` when `Z/2 wr_(Γ/⟨a_0⟩) Γ ∈ B_A`.
  - Then `BG ≤ L` gives `BG ∈ B_A`. ✓ (N1)
- **The finite-index step.** `H_4 ∈ B_A` implies `H_4 ⋊ C_4 ∈ B_A`, by the finite-extension closure node. ✓
- **The decidability caveat.** It is correctly placed. `Z/2 wr_(Γ/C) Γ` has solvable word problem only if membership
  in `C` is decidable, so no conclusion is possible without it (N3).

## The Labbé Attempt: hierarchy-phase gauges
- **The design fails, as the entry says.**
  - Each `E_a(z)` is a phase-multiplication operator conjugated by a word in the commuting permutation matrices
    `S_1, S_2`.
  - A diagonal matrix conjugated by a monomial matrix is again diagonal in the same basis. So all `E_a(z)` are
    diagonal in the phase basis and pairwise commute.
  - The family is then classical, and "Classical families" kills it by aperiodicity. ✓
- **The general lesson** is right as a necessary condition. See N4 for the precise form.

## Nits
- **N1 (item 2).** Name the isomorphism `W *_C (C × K) ≅ K *_(W/C) W`, valid for infinite `C`, as the step from the
  cited part 1 to the amalgam `L`. Part 3 of the cited node covers only finite `C`, and the "infinite-edge" remark
  sits in its Scope.
- **N2 (necessity).** Name the homomorphism explicitly: `BS(1,2) → Z`, `a_0 ↦ 0`, `a_1 ↦ 1`. It is well defined,
  and conjugate elements have equal images.
- **N3 (the caveat).** The natural choice `Γ = H_4 ⋊ C_4`, available when `H_4 ∈ B_A`, turns the caveat into the power
  problem for `a_0` in `H_4 ⋊ C_4`. Record it that way, with a source when one is found.
- **N4 (Labbé Attempt).** State the lesson precisely: "if every `E_a(z)` lies in one maximal commutative
  subalgebra, the family is classical". Local diagonal operators transported by frame-normalizing (monomial)
  holonomy are one instance. The phrase "non-monomial with respect to every local classical frame" is a heuristic
  necessary condition and should be marked as such.
