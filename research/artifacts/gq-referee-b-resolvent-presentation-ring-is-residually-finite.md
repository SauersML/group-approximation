# Referee report (citation/hypothesis lens): three items from lane gq-infinite-primes, on main at 8abfde57d

Referee: lane gq-referee-b, 2026-09-18.

**Items reviewed:**
1. `resolvent-presentation-ring-is-residually-finite(-proof)`;
2. the two new routes into `z-localized-embeds-in-fp-rf-group` that use
   `steinberg-groups-of-fp-rings-are-fp-in-rank-five`;
3. Attempt 1 of `resolvent-steinberg-rf-residual-is-finitely-normally-generated`, labelled heuristic.

## Verdicts

- **(1) PASS.** The three inputs are standard and used within their hypotheses. Gruenberg's location is unverified
  but not needed (R1).
- **(2) PASS.** The hypotheses of the rank-five node match `R_l` exactly.
- **(3) Correctly labelled heuristic.** Four imports should be marked "not read at source". Two of them are true and
  classical; see the list.

## (1) The residual finiteness of `R_l`

**Inputs.**
- **Free products of residually finite groups are residually finite.** Gruenberg (1957) is the standard source. The
  location "Thm 4.1, Cor. (ii), p. 44" comes from a search record and was not verified here.
  - **R1.** Nothing needs that theorem: `Z * C_m` is virtually free, as a free product of cyclic groups, and virtually
    free groups are residually finite.
  - Cite this elementary fact as primary, and Gruenberg as a pointer.
- **Uniqueness of reduced forms in free products.** Standard. Used correctly.
- **Lifting idempotents modulo a nilpotent ideal** (`l·M_d(Z/l^r)`). Standard. Used correctly.

**Proof checks.**
- **Finite modules.** All eight relations hold. At the wrap, `u + l = lN ≡ 0 mod l^r` because `l^{r−1} | N`;
  `u + 1` is invertible; `e` sits on `V_0`, where `u = 0`. **Correct.**
- **Idempotents.**
  - For `l` odd, `ε = (1+s)/2` in `F_l[C_2]`: `ε^2 = (2+2s)/4 = ε`.
  - For `l = 2`, `ε = 1+s+s^2` in `F_2[C_3]`: `ε^2 = 1+s^2+s^4 = ε`.
  - Both are `≠ 0, 1` and have a nonzero coefficient at `s`. **Correct.**
- **Independence of alternating words.**
  - Take `τ*` with the most `ε`'s. Its all-`g*` reduced word has `s+1` letters from `C_m`.
  - Every expansion term with an identity choice, or from a word with fewer `ε`'s, has at most `s` such letters.
  - Words with the same number of `ε`'s but different exponent tuples give different reduced words.
  - So the coefficient is `λ_{τ*}c^{s+1} ≠ 0`. **Correct.**
- **Transfer to a finite quotient** injective on the finitely many expansion elements. The coefficients are
  preserved, so independence survives in `F_l[Q]`. **Correct.**
- **Separation.** Both cases were checked at the level of the argument.
  - `δ ≠ 0`: a rational function has finitely many zeros.
  - `δ = 0`: minimal valuation `ν`, `N = l^ν`, lifts to `Z/l^{ν+1}`. Terms outside `F_0` act as `0`. `Y ≢ 0 mod l` by
    independence.
  - I did not re-derive the path normal form `resolvent-ring-has-path-normal-form` it rests on.

## (2) The rank-five routes

- **The rank-five node's hypotheses** (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`, statement verbatim): "Let
  `R = Z⟨g_1, …, g_d | ρ_1, …, ρ_l⟩` be a finitely presented unital ring and let `n >= 5`."
  - `R_l` has 5 generators and 8 relators, and the routes take `N >= 5`. **It matches.**
  - I passed that node's proof in `gq-referee-b-steinberg-direct-finite-presentation.md`.
- **`z-localized-fp-rf-via-resolvent-steinberg-rf-quotient`.**
  - `St_N(R_l)` is finitely presented. `K_rf` is finitely normally generated, by the first input. So
    `Λ = St_N/K_rf` is finitely presented and residually finite.
  - `R_l` residually finite (item 1) makes `E_N(R_l) ≤ GL_N(R_l)` residually finite. So `K_rf` maps to `1` in
    `E_N(R_l)`, and `Z_(l)` embeds in `Λ`.
  - **Correct.**
- **`z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l`.** It takes `N >= 5` from its first input.
  **Consistent.**

## (3) Attempt 1: statements to mark "not read at source"

- **"The twisted Laurent fundamental theorem gives a cokernel of `1 − σ` on `K_2(Q(u))` that contains `K_2(Q)`."**
  - The theorem is Farrell–Hsiang / Grayson, not read. Nobody has verified it.
  - "Contains `K_2(Q)`" needs injectivity of `K_2(Q) → K_2(Q(u))`, which follows from Milnor's exact sequence for
    `F(t)`. It also needs `(1 − σ_*)K_2(Q(u))` to meet the image of `K_2(Q)` trivially.
  - Both are plausible, but neither is checked. **Mark it unverified.**
- **"`K_2(Z/p^r) = 0` for `p` odd."** True: Dennis–Stein, *K_2 of discrete valuation rings* (Adv. Math. 1975), and
  standard. Mark it "not read at source".
- **"`K_2(Z_(l))` contains `⊕_{q≠l} F_q^×` (tame symbols)."** True in substance: Tate's `K_2(Q)`, plus injectivity of
  `K_2` of a DVR into `K_2` of its fraction field, with image the kernel of the tame symbol at `l` (Dennis–Stein).
  Mark both imports unverified.
- **"Centrality of `K_2(N,R)` for noncommutative `R` is itself not known here."** Honest.
  - The known criterion `n >= sr(R) + 2` (Voronetsky, arXiv:2004.08551v2, verified earlier) needs a stable-rank bound
    for `R_l`, which the node does not have.
- **Lane-internal steps, both correct:**
  - The trace argument `rank·l ≡ 0` (from `x u x^{-1} = u + l`, for free `Z/2^r`-modules).
  - The deduction that `eFe` has `l`-power characteristic, because `θ(Z_(l)) ⊆ eFe` makes every prime `q ≠ l`
    invertible.
