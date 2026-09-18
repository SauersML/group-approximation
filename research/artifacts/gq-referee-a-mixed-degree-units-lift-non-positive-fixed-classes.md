# Referee report (gq-referee-a, proof-gap lens): mixed-degree units lift non-positive fixed classes

**Reviewed:** `mixed-degree-units-lift-non-positive-fixed-classes` and its `-proof` (lane gq-infinite-primes,
48c3f0945), read on origin/main.

**Verdict: PASS** for items 1–3, which are unconditional. Item 4 is a correct implication from (CSL). There are four
nits. N2 replaces the sketchy step in item 1's index formula with a direct argument, and N3 adds a missing
positivity condition in item 3. (CSL) itself is for the citation lens.

## Item 1 (the author asked about this)
- *The core as a union.* `R_0` is spanned by the `s_α b t_β` with `|α| = |β|`. With `E_n = 1`, `S_nP^(n) = S_n`, so
  `R_0 = ∪ ι_n(P^(n)M(B)P^(n))`.
  - `ι_n` is unital: `ι_n(P^(n)) = (S_nT_n)^2 = 1`. It is multiplicative on the corner and injective, since
    `T_nι_n(c)S_n = c`.
  - The transition maps are `c ↦ φ(c)`: `S_(n+1)φ(c)T_(n+1) = Σ s_α(st)c_(αβ)(st)t_β = S_ncT_n`. ✓
- *Ultramatricial and cancellative* (N1). `B` is a product of `U_Q`-type rings. So `P^(n)M(B)P^(n)` is a corner of an
  ultramatricial ring, hence ultramatricial but not matricial, and `R_0` is ultramatricial.
  - Cancellation: equality in the colimit `K_0` is reached at a finite stage, which is semisimple, and there equal
    classes are equivalent. ✓
- *Levels.* `K_0` of the level-`n` corner is `K_0(B)` because `P^(n)` is full (N4).
  - With `A` invertible, the colimit is `Q^m` in level-0 coordinates.
  - For `w_g = gS` and `w_g' = Tg`, the domain `φ(g)` has class `A[g]` and the range `g` has class `[g]`. ✓
- *The index formula `[E] = A^(−1)[D]`* (N2). The proof's "differs from some `w_g` by degree-0 equivalences" is
  asserted, not shown. A direct argument:
  - `R_1 = Σ_i s_iR_0`, since `r = s(tr)` with `tr ∈ M_(k×1)(R_0)`.
  - For `w = EwD` and `w' = Dw'E`, put `c = tw` and `c' = w's`, with entries in `R_0`, since `tR_0s ⊆ M_k(R_0)`.
  - Then `c'c = w'w = D`, `cc' = tEs = φ(E)` and `cc'c = c`. So `D ~ φ(E)` in `R_0`.
  - `φ_* = A` in level-0 coordinates. At level 1, `φ(ι_1(c)) = tsc ts = c`, so the level-1 class `A^(−1)[c]` goes to
    `[c]`.
  - Hence `[D] = A[E]`. ✓

## Item 2 (the author asked about this)
- *The isometry.* `c = A^(−1)[1_B] ∈ [0,1]^m ∩ Q^m` is realized by an idempotent `g ∈ B`.
  - `[φ(g)] = [1_B]`, and cancellation gives `φ(g) = xy` and `yx = 1_B`.
  - `px = pφ(g)x = φ(g)x = x`. So `t_−t_+ = ypx = yx = 1` and `t_+t_− = sφ(g)t = g`. ✓
- *The corner skew Laurent structure.* `R_n = R_0t_+^n` and `R_(−n) = t_−^nR_0`, from `t_−^nt_+^n = 1`.
  - The universal corner skew Laurent ring maps onto `R`: `α(r)t_+ = t_+r` and `t_−α(r) = rt_−` hold in `R`.
  - In the universal ring, `rt_+^n = rα^n(1)t_+^n`. In `R`, `rt_+^n = 0` gives `rα^n(1) = rt_+^nt_−^n = 0`. So the map
    is injective in each degree. ✓

## Item 3 (the author asked about this)
- *The class bookkeeping.*
  - `ran_+ = A^(−1)dom_+ = A^(−1)v + b = v + b`, and `ran_− = A·dom_− = Ab`, the latter by item 1 applied to `w_−'`.
  - `dom_+ + dom_− − ran_+ − ran_− = (v + Ab) + b − (v + b) − Ab = 0`, which is `(1 − A^(−1))v = 0`.
  - `[dom w_+] − [ran w_−] = v`. ✓
- *The example* checks: `dom_+ = (2,2)`, `ran_+ = (1,0)`, `dom_− = (0,1)`, `ran_− = (1,3)`, and both totals are
  `(2,3)`.
- *Positivity* (N3). `ran_+ = v + b` must also be a nonnegative class. So `b` must satisfy `v + b ≥ 0` as well as
  `v + Ab ≥ 0`. `b = N·1` with `N` large does both, since `A ≥ 0` has positive row sums.
- *The assembly of `U` (the author asked about this).*
  - The pieces exist:
    - the idempotents with classes `ε·dom_±` and `ε·ran_±` lie already in `B`, pairwise orthogonal, for small `ε`;
    - `1 − D ~ 1 − E` by cancellation;
    - `w_+` is `c'·w_g·a`, where `a` realizes `D_+ ~ φ(g)` and `c'` realizes `g ~ E_+`, both of degree 0; `w_−` is
      built the same way.
  - The cross terms vanish: `w_aw_b' = E_aw_aD_aD_bw_b'E_b = 0` for `a ≠ b`, and likewise `w_a'w_b = 0`.
  - So `UU' = ΣE_a = 1` and `U'U = ΣD_a = 1`. ✓

## Item 4 (an implication from (CSL))
- *The boundary.* Given (CSL), `∂{λ,U} = λ ⊗ εv`.
- *`K_1` of the core.* `K_1(R_0) = Q^× ⊗ K_0(R_0)`. On each finite semisimple stage `K_1 = ⊕Q^×`, the maps are the
  multiplicity matrices, and `Q^× ⊗ −` commutes with colimits.
- *Infinite generation.* `λ ↦ λ ⊗ εv` is injective on `Q_(>0)`, which is free, because `K_0(R_0) ≅ Q^m` is
  torsion-free. So the image is not finitely generated, and the symbol lemma applies.
- *The final sentence.* If `ker(1−A) = 0`, then `coker(1−A) = 0`, and item 7(a) of the corner node applies
  unconditionally. Otherwise items 3 and 4 apply, conditionally on (CSL). ✓

## Nits
- **N1 (item 1).** "Hence matricial" should read "hence ultramatricial". The factors of `B` are `U_Q`-type.
- **N2 (item 1).** Replace the index-formula sketch with the `c = tw`, `c' = w's` argument above.
  - State the convention `w = EwD`, `w' = Dw'E` for partial isometries. The corner node's `w = ewe` issue shows
    it is needed.
- **N3 (item 3).** Require `v + b ≥ 0` as well as `v + Ab ≥ 0`, and note that `b = N·1` works.
- **N4 (item 1).** Note that `P^(n)` is full, so the corner has `K_0 = K_0(B)`. `A` invertible gives positive row
  sums, so `[p] = A[1_B]` is nonzero in every factor.
