---
rg: 2
id: torsion-defect-costs-nothing-in-bhm-germ-complexes
kind: claim
title: Nonzero germ defect is not a finiteness obstruction when the defects are torsion; a bounded full contracting RSG with finite defect group is F_infinity, because defect only splits the portraits of the BHM germ complex into finitely many orbits; defects at fixed singular points are always torsion, and a two-point half-shift element over the 3-shift gives an F_infinity example with defect 1 in Z/2
distinct_from:
  bounded-defect-free-full-contracting-rsgs-are-f-infinity: that needs zero defect for BHM's localization axiom; this drops the axiom, shows BHM's complex still works when defects are torsion, and so generalizes that theorem.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - bounded-defect-free-full-contracting-rsgs-are-f-infinity
```

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-19; Referee bh-ref-q12 2026-09-19: PASS with repairs.
Step 3 of the proof is wrong as written and is replaced, and the Example's `τ` is not a homeomorphism of the
3-shift and is replaced; the pentagon computations PASS. See the Referee section. Credit to Belk–Hyde–Matucci,
whose complex is used unchanged).
- Inputs: those of the parent node, i.e. BHM's germ complex, Matui's bisections, and the twisted-BT stabilizer
  reduction.
- Section 3 is analysis. No computation was run.

## Setting

- The setting and notation are those of `bounded-defect-free-full-contracting-rsgs-are-f-infinity`.
- `Δ` is the set of defects `d_g(p)` of singular germs, and `⟨Δ⟩` is the **defect group**.
- A B-germ `(Bh)_p` has the well-defined defect `d_h(p)`, since `d_{bh}(p) = d_b(hp) + d_h(p)` and B-germs are
  canonical.
- The **total defect** of a portrait `γ` is `Σ_p d(γ(p))`.

## Theorem

Let `L` be a bounded full contracting RSG with `⟨Δ⟩` finite. Then:
- `L` is `F_∞`;
- so are its finite-set stabilizers;
- `SV_L` is an `F_∞` simple group.

## Proof: BHM's argument with the localization axiom removed

1. **Zero-sum portraits are portraits of elements.** Let `γ` have germs `(Bg_i)_{p_i}` with total defect 0.
   - Replace `g_i` by `b_i g_i` (`b_i ∈ B`) so that the points `g_i(p_i)` are distinct.
   - Take disjoint small cones `U_i ∋ p_i`, avoiding the other singular points of `g_i`, with the sets `g_i(U_i)`
     pairwise disjoint.
   - Then `[E ∖ ⋃U_i] = [E ∖ ⋃ g_i(U_i)]`, because the total defect is 0. So a compact open bisection `k` of
     `G_Σ|_E` maps one onto the other (Matui, as in the parent node).
   - `h = g_i` on `U_i` and `h = k` elsewhere lies in `L`, and its portrait is `γ`.
   - Conversely, every element's portrait has total defect 0 (parent node, Proposition 2.2).
2. **Finitely many orbits (reworded per referee).**
   - Total defect is `L`-invariant for full portraits. It is **not** invariant for partial portraits: hidden
     points absorb germs, and `total(g·γ) = total(γ) − Σ_{p∈g(M)} d_{g^{-1}}(p)`.
   - The orbit count does not need invariance. Add a standard compensating set `Q_c` at fresh non-hidden points,
     realize the result by an `h` that is non-singular on `M` (cones chosen away from `M`), and apply `h`.
   - This leaves finitely many orbits of vertices and cubes of `K_{≤n}` for each `c`, and `c` ranges over the
     finite group `⟨Δ⟩`.
3. **Stabilizers (replaced per referee; the earlier version was wrong).** Already for a full zero-sum portrait
   `γ = portrait(h)`, `Stab(γ) = h^{-1}Bh`, which moves `sing(h)`.
   - **The data.** Let `γ` have labels `λ_i = (Bg_i)_{p_i}` outside its hidden set `M`, with total `c`.
   - **Build `τ`.**
     - Choose small disjoint cones `U_i ∋ p_i` avoiding `M`, with disjoint images.
     - Choose a clopen `E_c` with `[E_c] = [E] + c` containing the images (Matui).
     - A Matui bisection matches the complements. This gives a rational homeomorphism `τ: E → E_c` with
       `(Bτ)_{p_i} = λ_i`, canonical elsewhere.
   - **The stabilizer.** `Stab(γ) = τ^{-1}{k ∈ L_c : sing(k) ⊆ τ(M), k(τM) = τM}τ`, where `L_c ∈ 𝓕(L)` is the
     full RSG on `E_c` with the nucleus of `L`.
   - **Finiteness.** BHM Propositions 2.5 and 2.8, which do not use localization, make this group commensurable
     with `Fix_{V_(Σ,E_c)}(τM)`. That group is `F_∞`. Cubes are handled the same way, with `M ⊆ M'`.
4. **Links.** BHM's `K = ∏'_p T_p` and its Morse function do not involve the group. Descending links are joins of
   the discrete sets `Bgerm(L,p)` (BHM `prop:nConnected`), so `K_{≤n}` is `(n−1)`-connected.
5. **Brown's criterion** on `K_{≤n}` gives `F_n` for every `n`. The finite-set stabilizers and `SV_L` follow as
   in the parent node. The members of `𝓕(L)` have their defects in `⟨Δ⟩`. ∎

**So localization was used only to get transitivity on portraits.** The finite count of orbits is what Brown's
criterion needs.

## When the defect group is finite

- **Fixed points.** If `g(p) = p`, then `d_g(p)` is torsion.
  - `(B)_p` has finite index `m` in `(L)_p`, so `g^m`'s germ is canonical.
  - The cocycle rule at a fixed point gives `m·d_g(p) = d_{g^m}(p) = 0`.
- **One tail class.** If all singular points lie in one B-orbit, then every singular germ is a B-translate of a
  germ fixing a base point. So `Δ` is torsion, and `⟨Δ⟩` is finite (a finitely generated torsion abelian group).
- **Finite homology.** If `coker(I − A^T)` is finite, i.e. `det(I − A) ≠ 0`, then `⟨Δ⟩` is finite. This covers
  the full `d`-shifts: `Z/(d−1)`.
- **Open case.** A non-torsion `⟨Δ⟩` would require transfer germs between different tail classes whose defect has
  infinite order. Then `K_{≤0}` has infinitely many orbits. Whether that is a genuine obstruction, or only a
  failure of this complex, is **open**.

## Example: nonzero defect, and F_∞ (replaced per referee)

- **Withdrawn.** The earlier element `τ` (shifting the branches along `1^∞`) is not a homeomorphism: `C_0` is never
  hit. This is forced, because a germ of defect `1 ∈ Z/2` cannot be the only singular germ of a homeomorphism
  (parent, Proposition 2.2).
- **Replacement** (referee bh-ref-q12): the two-point element `g` on the 3-shift, with `B = V_(3,1)` and
  `H_0 = Z/2`, built from the half-shift `n: E → C_0 ⊔ C_1`, `n(0x) = 0n(x)`, `n(1x) = 02x`, `n(2x) = 1x`.
  - `g(0x) = 0n(x)`, `g(1y) = 1n^{-1}(y)`, `g(12x) = 02x`, `g(2x) = 2x`.
  - `g` is singular exactly at `0^∞` and `10^∞`, both with germ `n` and defect `1`.
  - Its singular points form one tail class, so `⟨Δ⟩ = Z/2` is finite.
- **Conclusion.** By the Theorem, with the repaired Step 3, **`L = [[⟨V_(3,1), g⟩]]` is `F_∞`**, although no element
  of `L` has exactly one singular point.

## 3. BBMZ hosts (analysis)

- **Free groups on a basis.** The nucleus is trivial, so `L = V_Σ`, which is `F_∞` (Matui). Nothing new.
- **Surface groups.** The BBMZ host is `F_∞` if two conditions hold:
  - (i) boundedness: no two distinct cycles in the non-identity part of the nucleus automaton are joined by a path;
  - (ii) `⟨Δ⟩` finite, for instance `det(I − A) ≠ 0` for the atom type graph of `Γ ∗ Z`.

  Both are finite computations from the type graph and the nucleus. Neither has been run. The pentagon evidence
  (4 persistent chains per generator) fits (i). These groups already have `F_∞` hosts through 2V, so this would
  test Question 1.2 and would not extend Zaremsky's answer.
- **Boundary dimension ≥ 2 (all Kazhdan cases).** Singular sets are expected to be uncountable (exponential
  activity), so this Theorem does not apply.

## Lesson for general BH

- **Obstructions and failures of method can be separated by counting orbits.**
  - An invariant that splits the portraits of a germ complex into finitely many orbits is only bookkeeping.
  - Torsion defect is of this kind: it destroys BHM's localization but not its finiteness proof.
- **What is left.** Only a non-torsion invariant, or uncountable singular sets, could be a genuine obstruction.
  - For Question 1.2 on hyperbolic hosts, the defect question is settled up to the torsion condition.
  - The real frontier is activity, which is driven by boundary dimension.

## Result of the two finite checks (09-19, right-angled pentagon group; artifact `gq-bh-finf-hyp-pentagon-activity-and-defect-check.md`)

- **Boundedness: evidence for.** Each generator has exactly 4 non-branching singular rays at levels 2–5.
- **`det(I − A) ≠ 0` fails.** The equitable shape coarsening of the atom type graph has
  `det(I − A_core) = 0`, with Perron value `φ²`. So the true type graph has eigenvalue 1, and `H_0(G_Σ)` is
  infinite.
- **Torsion is therefore undecided.** A reflection's singular germs come in pairs swapped across its wall, which
  are not covered by the fixed-point lemma.
- **Consequence.** For this surface-type example, the Theorem is conditional on torsion of those transfer
  defects. This is exactly the open non-torsion case above.
- This concerns `P` itself. The BBMZ host over `P ∗ Z` was not computed.

## Defect class of the pentagon reflection germs (09-19; artifact `gq-bh-finf-hyp-pentagon-defect-class.md`)

- On the coarse type graph `H_0 ≅ Z = ⟨x⟩`.
- Each reflection's 4 singular chains carry defect `+x, +x, −x, −x`, which cancel in pairs, at every tested level.
- By the surjection `H_0(true) → H_0(coarse)`, these defects have **infinite order** for the true types too.
- So the torsion criterion fails at the level of elements. The pentagon RSG is in the open non-torsion case: a
  Houghton-type integer flux across each wall.
- Whether this obstructs `F_∞`, or only this complex, is **open**.

## Referee (bh-ref-q12, 2026-09-19): Theorem PASS with repairs; Step 3 wrong as written and replaced; Step 2 reworded; Example replaced

**Checked against BHM** (arXiv:2407.03149, PDF read 09-19).
- **Definitions.** Portraits `p ↦ (Bg)_p`, and the action `g·(Bh)_p = (Bhg^(-1))_(g(p))`. The complex
  `K = ∏'_p T_p` has star trees `T_p`, and the Morse function counts hidden points.
- **Proposition 2.7.** The descending link of every vertex is the join of the discrete sets `Bgerm(G,p)` over
  its hidden points. This uses only the product-of-stars structure, not the action or localization. **Step 4 is
  correct.**

**Step 1: correct.** It needs `G_Σ|_E` purely infinite and minimal (the Matui bisection), and cones small enough
that both complements are nonempty.

**Step 2: correct after rewording.**
- Total defect is `L`-invariant for full portraits.
- It is **not** invariant for partial portraits. If `M` is the hidden set, then
  `total(g·γ) = total(γ) − Σ_(p ∈ g(M)) d_(g^(-1))(p)`, because hidden points absorb germs.
- The orbit count does not need invariance. The normal-form reduction works verbatim for partial portraits:
  - add `Q_c` at fresh non-hidden points;
  - realize the result by an `h` that is non-singular on `M` (cones chosen away from `M`);
  - apply `h`.
- This leaves finitely many orbits of vertices and cubes of `K_(≤n)` for each `c`, and `c` ranges over the finite
  group `⟨Δ⟩`.

**Step 3 is wrong as stated.**
- The stabilizer of a portrait with nontrivial labels need not preserve `P`, and it need not contain
  `Fix_B(P ∪ M')` with finite index.
- Already for a zero-sum full portrait `γ = portrait(h)`, `Stab(γ) = h^(-1)Bh`, which moves `sing(h)`.
- BHM's description `{g : sing(g) ⊆ M, g(M) = M}` holds only for non-singular portraits.

**Repair of Step 3.**
- **The data.** Let `γ` have labels `λ_i = (Bg_i)_(p_i)` outside its hidden set `M`, with total `c`.
- **Build `τ`.**
  - Choose small disjoint cones `U_i ∋ p_i` avoiding `M`, with disjoint images `g_i(U_i)`.
  - Choose a clopen `E_c ⊆ E` with `[E_c] = [E] + c` that contains the images. In a purely infinite minimal
    groupoid every class is realized inside any nonempty clopen (Matui).
  - The classes of `E ∖ ⋃U_i` and `E_c ∖ ⋃g_i(U_i)` agree (by the total-`c` computation), so a Matui bisection
    maps one onto the other.
  - This gives a rational homeomorphism `τ: E → E_c` with `(Bτ)_(p_i) = λ_i`, canonical everywhere else.
- **The stabilizer.**
  - `g·γ = γ` exactly when `g(M) = M` and `τ g τ^(-1)` has canonical germs off `τ(M)`.
  - So `Stab(γ) = τ^(-1) {k ∈ L_c : sing(k) ⊆ τ(M), k(τM) = τM} τ`, where `L_c` is the full RSG on `E_c` with
    the nucleus of `L`, a member of `𝓕(L)`.
  - Here `τ`-conjugation preserves `L`-germs, and fullness puts the conjugates in `L`.
- **Finiteness.** BHM Propositions 2.5 and 2.8 do not use localization. They make this group commensurable with
  `Fix_(V_(Σ,E_c))(τM)`, which is `F_∞` (parent node, item (2)). Cubes are handled the same way, with `M ⊆ M'`.
- **With this repair Step 3 holds.**

**Step 5: correct** (Brown's criterion via Geoghegan 7.3.1, as in BHM Theorem 2.1).
- The finite-set-stabilizer and `SV_L` clauses inherit the unreviewed twisted-BT node, as in the parent.

**Torsion criteria: correct.**
- **Fixed point.** By finite index, some power `g^k` has canonical germ at `p`, and the cocycle gives
  `k·d_g(p) = 0`.
- **One tail class.** Move the target back by `B` to get a germ that fixes a point, with the same defect.
- **`det(I − A) ≠ 0`.** Then `coker(I − A^T)` is finite.

**The Example as written is not a homeomorphism.**
- `τ` sends each branch along `1^∞` to the next one, so `C_0` is never hit and `τ(E) = E ∖ C_0`. So
  `⟨V_3, τ⟩ ≤ Homeo(E)` is undefined.
- This is forced: a germ of defect `1 ∈ Z/2` cannot be the only singular germ of a homeomorphism (parent,
  Proposition 2.2).
- **Replacement.** Use the two-point element `g` from the parent's referee section. It is singular at `0^∞` and
  `10^∞`, both germs of the half-shift `n` with `n² = (x ↦ 0x)`, and both have defect 1.
- Its singular points form one tail class. So the Theorem, with the repaired Step 3, gives
  **`L = [[⟨V_(3,1), g⟩]]` is `F_∞`**, while no element of `L` has exactly one singular point.

**Credit.**
- This Theorem proves BHM Remark 2.13 for bounded full contracting RSGs with finite defect group, using BHM's
  complex unchanged. Credit the statement and the complex to Belk–Hyde–Matucci. The lane's contribution is the
  orbit count that replaces localization.
- No prior source found for the torsion case (searches 09-19, as in the parent).
- The non-torsion case is correctly stated as open. The pentagon addenda (7e5910d5a1, 4c2b83e595; reviewed
  below) place that example in it.

**Verdict: PASS with repairs** (Step 2 wording, Step 3 replaced, Example replaced).

### Pentagon computations (7e5910d5a1, 4c2b83e595): PASS as computation, with three repairs to the readings

The scripts (in the two artifacts) were read, and the printed data were rechecked by hand.
- **Coarse type graph.** `A = [[0,5,5,0],[0,2,0,1],[0,1,2,0],[0,0,1,0]]`.
  - It reproduces the atom counts `1, 10, 30, 80, …` level by level.
  - Its core has characteristic polynomial exactly `x(x−2)² − 1 = (x−1)(x²−3x+1)`. So `det(I − A_core) = 0`,
    with Perron value `φ²`.
  - The "consistent with" of 7e5910d5a1 is therefore exact.
- **Coarse `H_0 ≅ Z`.** Relations `e_3 = e_2`, `e_1 = −e_2`, `e_0 = 5(e_1+e_2) = 0`. Each eliminates a generator
  with coefficient `±1`, so the quotient is free of rank 1 on `x = [e_2]`, with no torsion.
- **Defect vectors.** `(0,0,1,0) ↦ x` and `(0,1,−1,1) ↦ −x`. Both have infinite order, and the four chains cancel
  in pairs. That is Proposition 2.2 of the parent; for the involution `k`, it also follows from `d_(k²) = 0`.
- **What `defectclass.py` computes.** It computes `[kD] − [D]` in coarse `H_0` for chain atoms `D` at levels
  `2–4`.
  - Exactness of `kD = ⊔A'_i` is checked forward on the sphere points of `D`, and backward through the involution
    `k` on independent sample points (levels `R0 ± 1`). So it computes what the node claims, on the sampled data.
- **Transfer to the true types.** This is correct. Shapes are determined by true types, and the partition is
  equitable, so `AP = PQ` for the type-to-shape incidence `P`.
  - Transposing gives `P^T(I − A^T) = (I − Q^T)P^T`. So `P^T` induces a surjection
    `H_0(true) → H_0(coarse)` that sends cone classes to cone classes.
  - A true defect whose image is `±x` has infinite order.
  - The same identity gives the spectral inclusion used in 7e5910d5a1. So the true `H_0` is infinite, and the
    reflection germs have infinite-order defect.
- **Evidence, not proof.** Three inputs are finite-depth data:
  - that the shape partition is stable and equitable ("stabilized at `D = 2`", `inconsistent = 0` on levels
    `≤ 7`);
  - exactness of atoms to level 7;
  - boundedness, from 4 non-branching chains at levels `2–5`.
- **Repairs to the readings in the defect-class artifact.**
  1. "`SingFix(M,M)` are extensions of `Fix_B(M)` by finite-index subgroups of `Z^(|M|−1)`" is wrong.
     - An element fixing `M` has torsion defect at each point of `M` (fixed-point lemma), so its defect is 0 in
       the free part.
     - The correct statement is BHM Proposition 2.8: `Fix_B(M)` has finite index in `SingFix(M,M)`.
     - The conclusion `F_∞` is unchanged.
  2. "Cannot be recoded away (Bowen–Franks invariance)" holds only for recodings that induce an isomorphism of the
     groupoid `G_Σ`. A different coding SFT, with a different base group, is not covered.
  3. Scope: this is `P` on `∂_h P`, not the BBMZ host over `P ∗ Z`, as the artifacts say. The Houghton
     comparison is heuristic.
