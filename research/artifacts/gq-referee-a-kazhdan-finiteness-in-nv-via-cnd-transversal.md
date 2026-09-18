# Referee report (gq-referee-a, proof-gap lens): Kazhdan finiteness in nV from the transversal cnd function

**Reviewed.** Two conditional routes by lane gq-nv-obstruct, read on origin/main:
- `kazhdan-finiteness-in-nv-via-cnd-transversal` (4bfc08e51);
- `gl-3-z-in-no-nv-via-cnd-transversal` (93792b520).

**Verdict: PASS for both routes as conditional deductions.** Their key input,
`brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` (`ψ_1`), is OPEN, so neither target is
reached.

## 1. `kazhdan-finiteness-in-nv-via-cnd-transversal`

- **Step 1 (automorphisms).** Correct. Branches of `nV` are products of prefix replacements. Conjugating
  by a coordinate permutation of `C^n` permutes the bricks and the prefix data, so `α_σ` preserves `nV`
  and is an automorphism. `α_σ(T_n) = T_n^σ` is the triangular subgroup for the order
  `σ(1), …, σ(n)`.
- **Step 2 (covering).** Correct.
  - Property (T) gives (FH) (Delorme–Guichardet), so `ψ_1` is bounded on `K' = σ^{-1}Kσ`.
  - A subgroup that meets `r` left cosets `g_iT_n` is a union of at most `r` cosets of `K' ∩ T_n`.
  - Conjugating back gives `[K : K ∩ T_n^σ] < ∞`.
- **Step 3 (the intersection, the point I was asked to push).** Correct.
  - For `n ≥ 2`, take `i = 1` in the triangular condition for `T_n^{σ_j}`. Then `g` and `g^{-1}` map
    fibres of `x ↦ x_j` into fibres, so `g(x)_j = h_j(x_j)` with `h_j` bijective.
  - On a brick `∏u_iC`, `g` is `∏(u_i → v_i)`, so `h_j = (u_j → v_j)` on `u_jC`.
  - Finitely many such cones cover `C`, and their common refinement is a finite cone partition on
    which `h_j` is canonical. Since `h_j` is bijective, the image cones partition `C`. So `h_j ∈ V`.
  - Hence `⋂_j T_n^{σ_j} = V^n`, and the reverse inclusion is clear. A finite intersection of
    finite-index subgroups has finite index.
- **Step 4 (finish).** Correct. `Σψ_V(h_i)` is a proper cnd function on `V^n` (Farley). `K ∩ V^n` has
  (T) and the Haagerup property, so it is finite, and so `K` is finite.
- **Byproduct (`ψ_1` exists iff a cnd function proper modulo `V^n` exists).** Correct.
  - Normalized cnd functions are `≥ 0`, so a sublevel set of the sum lies in each summand's sublevel
    set.
  - `gA ∩ hB` is empty or a coset of `A ∩ B`.
  - `V^n ≤ T_n` gives the converse.
- **Refutation test.** Correct. By Burger, `(Z^2 ⋊ F, Z^2)` has relative (T) when `F ≤ SL_2(Z)` is
  non-amenable, and the restriction of a cnd function on `nV` is cnd on the subgroup.

## 2. `gl-3-z-in-no-nv-via-cnd-transversal`

- **m = 1.** `H_3(Z) ≤ GL_3(Z)`, and `thompson-v-has-no-heisenberg-subgroup` excludes it from `V`.
  Consistent with Higman's theorem that torsion-free nilpotent subgroups of `V` are free abelian.
- **m ≥ 2, steps 1–4.** Correct: (T), then bounded, then finite index in `T_m`, then a power of
  `ι(e_12)` lies in `T_m`.
- **Step 5.** It rests on item 3 of `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`, which
  that node marks "unreviewed by a verifier lane". I did not review it. The route is sound given it.
- **Redundant, given the first route.** With `ψ_1`, route 1 already makes `SL_3(Z)` (infinite, (T))
  impossible in `nV`. So step 5 and its unreviewed input are needed only if one wants the weaker
  cubical-free statement. The first route needs only Farley.

## 3. For the coordinator

- Both routes are correct reductions to the single OPEN claim `ψ_1`.
- Route 1 is the stronger and cleaner one: it gives all Kazhdan subgroups finite, answers Zaremsky
  2.19(a), (c) and (d), and needs no triangular-subgroup analysis.
- For the GL_n(Q) root, neither route settles anything until `ψ_1` is constructed.
