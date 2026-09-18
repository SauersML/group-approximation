---
rg: 2
id: keyed-diversification-slots-give-plane-constant-minimal-lifts
kind: route
title: A Lambda_0-constant Durand--Romashchenko hierarchy with per-plane tables and diversification slots keyed by each plane's own table lifts a free effective minimal subshift to a minimal free SFT on Lambda_0 x Z^2
target: free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2
requires:
  - durand-romashchenko-minimal-sft-simulation
---

**Proof (lane proof at design level, bh-g1-simulation, 2026-09-18; unreviewed).**
- The fixed-point machinery is DR's, read at source (arXiv:1802.01461). The references are: the
  self-simulating tiling with variable zoom (§2.5), the input fields (i)–(vi) of letter delegation
  (§4.1), frames of diversification slots with properties (p1)–(p4) (§3.2 and §5), Lemma
  `lemma-clones-with-embedded-bits`, and Cases 1–3 of the proof of Theorem 7.
- Everything specific to `Λ_0` is written out below.
- The per-plane tables and twin checks are those of Attempt 2 on
  `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`.

**Conventions.**
- `S` is a finite symmetric generating set of `Λ_0`.
- The action is `(g·y)(h) = y(g^{-1}h)`, and neighbours are `h ~ hs`.
- `F_k = B_{Λ_0}(r_k)`, with `r_k` computable, nondecreasing and unbounded, and slow enough for
  condition (G) below.
- The **table** of plane `λ` at level `k` is `T_λ|F_k`, where `T_λ(f) = y(λf)`.

## Construction of X

1. **(L) Letters.** `ℓ(λ,z) ∈ B`, constant on each plane `{λ} x Z^2`. Put `Φ(x)(λ) = ℓ(λ,0)`.
2. **(H) Skeleton.** A DR self-simulating hierarchy on `Z^2` with variable zoom `N_k`, copied
   along `Λ_0`: the skeleton symbol at `(λ,z)` equals the one at `(λs,z)`.
   - Positions, levels, computation zones, wires, borders and slot frames are therefore the same
     in every plane.
   - Every bit of every level's input fields has a canonical carrier cell, fixed by the skeleton.
3. **(T) Tables.** Every level-`k` macro-tile of plane `λ` carries, as input fields replacing DR's
   letter chunks (iv) and (v):
   - `τ_k ∈ B^{F_k}`, its own table;
   - `τ_k^{(s)}` for `s ∈ S`, copies of the neighbours' tables;
   - `τ_{k+1}`, its father's table.

   The rules are:
   - **Base.** At level 0, `τ_0(1) = ℓ`.
   - **Within a plane.** Children's `τ_k` and fields `τ_{k+1}` agree with the father on the
     overlaps. This is DR's delegation coherence, with the zone of responsibility replaced by the
     plane.
   - **Twin rule (local).** The carrier cell of each bit of `τ_k^{(s)}` in plane `λ` equals the
     carrier cell of the same bit of `τ_k` in plane `λs`. The two cells sit at the same
     `Z^2`-position.
   - **Zone check.** `τ_k(sf) = τ_k^{(s)}(f)` whenever `f, sf ∈ F_k`, and `τ_k` contains none of
     the first `t_k` forbidden patterns of `Y`, with `t_k → ∞`.
4. **(C) Computations.** DR's, with the input fields above. Only the twin rule refers to another
   plane, and it involves table carriers only. Computation symbols, wire bits and border data are
   never compared across planes.
5. **(D) Keyed slots.** Fix a level `K` and a window type `π`: a position of a 2×2 window of
   level-`(K-1)` macro-tiles that touches a computation zone, a wire or a border of level-`K`
   macro-tiles. Border windows may straddle two or four fathers, as in DR §5.
   - `Adm_π(τ)` is the finite set of assignments of the non-table, non-position part of the
     identities in window `π` that are realizable with table data `τ`.
   - For each `π` and each map `i` with `i(τ) ∈ Adm_π(τ)` for all `τ ∈ B^{F_K}`, reserve a slot
     with a DR frame in the free zone of every level-`K` macro-tile.
   - The frame tiles read `(π, i)` from their position and `τ_K` from their father-table field.
     They force the slot's inner window to believe it sits at `π`, with identities `i(τ_K)` and
     the real table fields. This is DR's property (p2), with the displayed pattern computed
     rather than fixed.
6. **(G) Growth.** Slot counts must fit and evaluations must terminate in time.
   - The number of window types is `O(N_K log N_K)`, and each `|Adm_π| ≤ c`.
   - It is enough that `|B|^{|F_K|} ≤ log log N_K`. Then the slot count is
     `N_K^{1+o(1)} · (log N_K)^{log c} ≪ N_K^2`.
   - `i(τ_K)` is then computable inside a level-`(K-1)` zone, in time `poly log N_K`, which is
     `poly log N_{K-1}` for DR's doubly exponential zoom.

## Proof

1. **X is an SFT.** All rules are local.
2. **All tables are true (determination).** Let `x ∈ X` and `y = Φ(x)`. We claim
   `τ_k = T_λ|F_k` in every plane `λ` and at every level `k`.
   - Induction on `|f|`, simultaneously for all planes.
   - `f = 1` holds by the base rule and within-plane coherence.
   - For `f = sf'`: `τ_k^λ(sf') = τ_k^{(s),λ}(f') = τ_k^{λs}(f') = y(λsf')`, by the zone check,
     the twin rule, and induction in plane `λs`.
   - *Consequences.* Every forbidden pattern of `Y` is eventually tested on every ball, so
     `y ∈ Y`. For `y ∈ Y` and a generic skeleton, the configuration with true tables passes every
     check, so `X ≠ ∅` and `Φ` is onto. The two clauses of the statement hold by construction.
3. **Freeness.** Suppose `(λ,z)·x = x`.
   - Applying `Φ` gives `λ·y = y`, so `λ = 1` because `Y` is free.
   - Then the skeleton is `z`-periodic, so `z = 0`, because DR hierarchies are aperiodic.
4. **Plane clones lemma.** Take two windows of level-`j` macro-tiles in planes `μ` and `μ'`
   with:
   - (a) the same positions with respect to their fathers and grandfathers;
   - (b) the same identity assignment from their fathers (space-time pattern, wire bit or
     border data);
   - (c) `T_μ = T_{μ'}` on `F_{j+2}S`.

   Then the two windows are equal. This is DR's induction on rank: (a)–(c) fix all input fields,
   including the neighbours' copies and the fathers' tables. Tables are plane-constant, so DR's
   zone-of-responsibility and alignment conditions do not arise.
5. **Separation.** For each `g ≠ 1` there is `ρ(g)` such that `y` and `g·y` differ on `B(ρ(g))`
   for every `y ∈ Y`.
   - *Reason.* The sets `{y : y = g·y on B(ρ)}` are closed and decreasing, and their intersection
     `Fix(g)` is empty, so one of them is empty by compactness.
   - *Consequence.* For finite `F` and `F_K ⊇ B(max_{g ∈ F^{-1}F \ 1} ρ(g))`, the tables
     `T_{λ'f}|F_K`, `f ∈ F`, are pairwise distinct, for every `λ'` in every configuration.
   - *Check.* With `a = λ'f` and `b = λ'f'`, `y(bμ) = (g·y')(μ)` for `y' = a^{-1}·y` and
     `g = b^{-1}a`.
6. **Minimality.** Let `P` be a pattern of some `x ∈ X` on `λF x Q`, with `Q ⊆ Z^2` a square.
   - **Windows.** Choose `k` with `Q` inside a 2×2 window of level-`k` macro-tiles, and
     `K ≥ k+1` as in step 5. In each plane `λf`, let `W_f` be the 2×2 window of level-`(K-1)`
     macro-tiles containing `Q`. It is at the same `Z^2`-position in every plane.
   - **What fixes them.** By step 4, the tuple `(W_f)` is fixed by its skeleton type, its
     identity tuple `(σ_f)`, and `T_{λf}` on `F_{K+1}S`.
   - **Skeleton-only windows.** Here `σ_f` depends on the skeleton alone, and siblings with the
     same type occur in every level-`(K+1)` macro-tile of every plane.
   - **Other windows.** Here `σ_f ∈ Adm_π(T_{λf}|F_K)`. Take any `λ'` with
     `T_{λ'f} = T_{λf}` on `F_{K+1}S` for all `f ∈ F`.
     - By step 5 the keys `T_{λ'f}|F_K` are distinct, so some admissible `i` sends each to
       `σ_f`.
     - The slot `(π, i)` of every level-`K` macro-tile shows `σ_f` in plane `λ'f`.
     - Take such macro-tiles at the same position in their fathers as the original fathers. By
       step 4 their slots reproduce `(W_f)`, and hence `P`.
   - **Finding `λ'`.** `Y` is minimal, so the pattern of `y` on `λF F_{K+1} S` recurs within a
     bounded distance `R(P)` in every `y'' ∈ Y`. The slots, or siblings, recur in `Z^2` with
     step `L_{K+2}`. The choices in `Λ_0` and in `Z^2` are independent (mechanism 1).
   - **Conclusion.** `P` occurs within bounded distance of every site of every `x'' ∈ X`, so `X`
     is minimal. `∎`

## What is not checked here

- **DR details.** The frames and the realizability of every admissible identity are DR's,
  adapted rather than re-derived. That covers the transfer of (p1)–(p4) to keyed slots and of
  border slots to windows straddling infinite faults.
- **Computability of `Adm_π(τ)`.** A level-`(K-1)` tile with a syntactically legal identity is
  realizable iff its bounded zone computation accepts. That computation reads real tables, which
  pass every finite check, so `Adm_π(τ)` is decidable in bounded time. This is a sketch.
- **Reading pressure.** Only `2|S|` twin comparisons per carrier cell, so none arises.

## Referee (bh-ref-e1-b, 2026-09-18): PASS, with one repairable design gap

Independent referee 1 of 2. I read Durand–Romashchenko at source (arXiv:1802.01461, TeX of v4):
§3.2 "Enforcing minimality" with (p1)–(p4) and Cases 1–3, the slot frame of their Fig. "A
diversification slot", the letter-delegation scheme (§4.1, zone of responsibility), and the
minimal-simulation proof with its Claims 1–5.

**Checked and correct.**
- **Locality.** Every rule, including the twin rule between `(λ,c)` and `(λs,c) = (λ,c)·(s,0)`,
  is a rule on a bounded window, so `X` is an SFT. The conventions `(g·y)(h) = y(g^{-1}h)`,
  neighbours `h ~ hs` and `T_λ(f) = y(λf)` are consistent throughout.
- **Determination (step 2).** The induction on `|f|` is sound: for geodesic `f = sf'` both `f'`
  and `sf'` lie in `F_k`, and within-plane coherence makes every level-`k` macro-tile of a plane
  carry the same table. Occurrence of a pattern `p` of `Y` at `λ` is `T_λ|_{supp p} = p`, so the
  zone checks with `r_k, t_k → ∞` give `y ∈ Y`.
- **Freeness (step 3).** Correct as written.
- **Separation (step 5).** The compactness argument and the identity
  `T_{λ'f'} = (g·y')` on `F_K` with `y' = (λ'f)^{-1}·y` and `g = f'^{-1}f ≠ 1` are correct. So the
  keys on any finite window of planes are pairwise distinct. This is exactly where freeness of `Y`
  is spent, and it is the right place.
- **Transverse factors (mechanism 1).** Correct, and the comparison with DR is accurate. DR need
  the standard embedding (their Claims 1–2 of the minimal-simulation proof) because the input and
  the macro-tile grid share the horizontal direction. Here a macro-tile in plane `λ` sees the table
  of `λ` whatever its `Z^2`-position, so recurrence in `Λ_0` and in `Z^2` are chosen independently.
- **Minimality (step 6).** The argument has the right shape: Case 1 (skeleton blocks), wire and
  computation-zone windows via slots, border windows as in DR's border slots. One slot `(π, i)` at
  a single plane-constant position serves all planes `λ'f` at once, because the keys are distinct.
  A 2×2 window of level-`k` macro-tiles lies in a 2×2 window of level-`j` macro-tiles for every
  `j ≥ k`, so the choice of `K` is legitimate.
- **Capacity (G).** DR's slots are indexed by (position, filling) with `O(1)` fillings per position.
  Keyed slots multiply this by the number of maps `i`, which is `c^{#keys}`. Under (G) the total is
  `N_K^{1+o(1)}`, and it fits in the free area as DR's border slots already do.

**Gap G1 (repairable): the key is too small for the admissibility it must respect.**
- As written, `i` is keyed by `τ_K = T|_{F_K}` only, and must satisfy `i(τ) ∈ Adm_π(τ)` for every
  `τ ∈ B^{F_K}`. But a window `π` that touches the bottom row of the level-`K` computation zone, or
  a wire carrying an input field, displays bits of the level-`K` macro-tile's other inputs:
  `τ_K^{(s)}` (which is `T` on `sF_K`, outside `F_K`) and `τ_{K+1}`.
- Whether an assignment `σ` of computation, wire or border bits is locally admissible next to
  those input bits therefore depends on data the key does not see. Two planes with the same
  `τ_K` but different `τ_{K+1}` or `τ_K^{(s)}` receive the same display `i(τ_K)`, which can be
  illegal in one of them. If that happens, the local rules exclude every configuration containing
  that plane table, so `X` could be empty or `Φ` not onto.
- If the fake carriers inside a slot also trigger the twin rule (skeleton symbols are the fake
  coordinates, as in DR's frame), then `i(τ_K^μ)` must also agree with `i(τ_K^{μs})` on
  `τ^{(s)}`-bits. That is again a condition on data outside `F_K`.
- Step 6 already quietly uses `T` on `F_{K+1}S`, which is where the real dependence lies.
- **Repair.**
  - Let every level-`(K-1)` child carry the full input field `κ_K = (τ_K, (τ_K^{(s)})_s, τ_{K+1})`
    of its level-`K` father, with the same coherence rule as for `τ_K`.
  - Key the slots by `κ_K`, which is a function of `T` on `F_{K+1} ∪ ⋃_s sF_K ⊆ F_{K+1}S`.
  - Display the real `κ_K` bits in the fake window, so that twin checks inside slots compare real
    data, and let `Adm_π(κ)` be the admissible non-table bits next to them.
  - Step 5 still gives distinct keys, since distinct `τ_K` give distinct `κ_K`.
  - (G) becomes `|B|^{|F_{K+1}|(|S|+2)} ≤ log log N_K`. That still holds for a slowly growing
    computable `r_k`, since DR's variable zoom allows `log log N_K → ∞`.
  - Nothing else in the proof changes.

**Gap G2 (cosmetic).** `Adm_π(τ)` is empty for tables that no point of `Y` realizes, so "for all
`τ ∈ B^{F_K}`" admits no `i` at all. Take `i` partial: defined where `Adm ≠ ∅`, and arbitrary
elsewhere, since those keys never occur in `X`.

**Not re-derived (design level, as the node says).**
- That DR's frames, with (p2) 2×2-determinacy, force a *computed* display. The frame tiles are
  level-`(K-1)` macro-tiles that know their real coordinates, so they can decode `(π, i)` and
  evaluate `i(κ_K)` in time `poly log N_K`. I find this plausible and consistent with DR §3.2, but
  it is not written out.
- Border slots for windows on infinite faults, which the node takes from DR.

**Verdict.** PASS as a design-level proof, conditional on repair G1, which is local and does not
touch the argument's structure. Credit: the frame, slot and variable-zoom machinery is
Durand–Romashchenko's (arXiv:1802.01461, and Durand–Romashchenko–Shen for fixed-point tilings).
The new ideas here are the transverse `Z^2` factor and keying the slots by each plane's own table.
