# Swarm notes: sofic-groups-embed-in-simple-kazhdan-sofic-groups (2026-09-16)

Lane `swarm-sofic-groups-embed-in-simple-k`. Target claim: every finitely generated sofic group embeds in an infinite
simple Kazhdan sofic group. Everything here is unreviewed.

## Setup

- **The candidate host.** The graph already has the rank-metric version of the target
  (`sofic-groups-simple-kazhdan-linear-sofic-envelope-proof`):
  - `Δ = C(Γ)` is the half-line overgroup, with `Γ ≤ [Δ,Δ]`;
  - `L = Z/2 ≀ Δ` acts on `2^Δ`, `R_Δ = LC(2^Δ,F_2) ⋊ L`, and `G_Δ = EL_3(R_Δ)`;
  - `G_Δ` is simple, Kazhdan, `F_2`-linear sofic and contains `Γ`.

  What is missing is Hamming soficity of `G_Δ` when `Γ` is not LEF.
- **The previous lane.** sk-sofic-almost-action (2026-09-14, `research/artifacts/sk-sofic-almost-action-plan-2026-09-14.md`)
  showed that Kazhdan cut-downs of column models `EL_n(𝒜_N) ↷ W_N^n` certify only LEF groups, but only when the image
  algebras `𝒜_N` are semisimple. The radical case was its target T5.
- **This lane** attacked T5.

## What was established (unreviewed)

1. **Theorem G.** `elementary-group-column-actions-have-orbitwise-gap`, direct route
   `elementary-group-column-actions-orbitwise-gap-proof` with `requires: []`.
   - *Statement.* For any unital ring `𝒜`, finite module `W`, `n ≥ 2` and `EL_n(𝒜) ≤ H ≤ GL_n(𝒜)`: an additive `g`
     that moves fewer than `|O|/(2n²)` points of an `H`-orbit `O ⊆ W^n` fixes `O` pointwise.
   - *Proof.*
     - `P = Fix(g)` is a subgroup, and root-subgroup orbits are cosets `x + (𝒜x_j)e_i`.
     - A coset not inside `P` has at least half its points outside `P`.
     - So the bad root cosets cover at most `2m` points for each `(i,j)`, and the swaps
       `s_ij = e_ij(1)e_ji(−1)e_ij(1)` handle the diagonal positions.
     - Counting `n²` bad sets gives an orbit point `x` with `(𝒜x_j)e_k ⊆ P` for all `j,k`.
     - Hence `O ⊆ L(x)^n ⊆ P`.
2. **Corollary C′ and the host consequence.** `column-model-kazhdan-cut-downs-certify-only-lef`, route
   `column-model-kazhdan-cut-downs-lef-proof`.
   - *C′.* Established Corollary C needs only a common orbitwise gap of the images `ρ_N(H)`. I re-read its proof,
     steps 1–5 of `orbitwise-gap-sofic-approximations-local-embeddings-proof`. It uses `ρ_N` only as a homomorphism
     into permutations of a finite set, plus invariance of the gap under restriction. So C′ holds for every unital
     ring homomorphism `R → End(W_N)`, radical allowed.
   - *Host consequence.* If `[Δ,Δ]` is not LEF, no `F_2`-linear column model of `EL_n(F_2⟨B⟩)` certifies soficity of
     `G_Δ` or of `EL_3(F_2[Δ])`. The letters may go to arbitrary matrices, with any almost invariant sets of vectors.
     The reason is `[Δ,Δ] ≤ EL_3(F_2[Δ]) ≤ G_Δ` (Whitehead) and LEF passing to subgroups.
3. **Reduction.** Route `sofic-envelope-from-sofic-lamplighter-host` reduces the target to one open claim,
   `sofic-lamplighter-host-elementary-groups-are-sofic`.
   - The open claim: `EL_3(R_Δ)` is sofic for every finitely generated infinite sofic `Δ`. The case `Δ = C(Γ)`
     suffices.
   - The other steps are established nodes: the half-line overgroup, the binary simplicity criterion, Ershov–Jaikin (T)
     and the Whitehead embedding. Minimality and topological freeness are restated in the route.
   - The new open claim has an `## Attempts` section listing the dead routes.

Outcome for the target: an obstruction to one natural family of approximations, plus a reduction. The target stays
open.

## Approaches tried and where each dies

- **Column models with a radical (T5): closed** by Theorem G, as an obstruction. No column model helps.
- **Linear cellular automaton view of the counting rank models.**
  - The configuration-space models of `sofic-lamplighter-bernoulli-crossed-products-have-rank-models` are linear
    cellular automata on sofic graphs, and they fail only at `εN` bad base points.
  - On vectors, a nonzero matrix error `x` with `rk(x−1) = r` fixes a `2^(−r)` fraction of the points, so the Hamming
    defect is at least `1/2`.
  - Dies: the same barrier as `rank-models-give-no-hamming-models-through-vector-actions`.
  - Cutting down to almost invariant sets of vectors is exactly the column-model case, now closed by C′.
- **IRS view of T3.**
  - A cut-down of genuine finite `H`-sets `Z_N` is a sofic approximation of `G = H/K` iff the stabilizer IRSs `μ_N` of
    `H` converge weak-* to `δ_K`. Relators have `Pr(k ∈ Stab) → 1`, and non-relators `Pr(h ∈ Stab) → 0`.
  - So T3 asks which finite-action IRSs of a Kazhdan `H` can converge to `δ_K` for a non-LEF quotient.
  - Theorem O with the cutting lemma says: none whose actions have a common orbitwise gap. Theorem G says column
    models always have one.
  - This is a reformulation, not progress on the remaining cases.
- **Marked limits.** Presenting `G_Δ` as a marked limit of LEF groups, for instance through hosts over LEF marked
  approximations of `Δ`, dies: marked limits of LEF groups are LEF, and `G_Δ` is not LEF when `[Δ,Δ]` is not.
- **Lie-type finite quotients: partial.**
  - For genuine `H`-sets factoring through finite simple groups of Lie type, transitive fixed-point ratios are bounded
    by primitive ones, because the fibres of `H/L → H/M` have equal size.
  - Liebeck–Saxl-type bounds (not read at source) would then give a common gap.
  - Dies for finite quotients with a normal unipotent radical: their elements can act trivially on every primitive
    quotient while being nontrivial.
- **Not covered, and still live (M2′):**
  - affine actions `x ↦ ρ(h)x + c(h)`, where `T_ij`-orbits need not be cosets because `a ↦ (ax_j)e_i + c(e_ij(a))` is not
    additive;
  - tensor, adjoint and exterior-power representations, where root subgroups act polynomially of degree `> 1`;
  - coset spaces of finite quotients with non-vector stabilizers, such as flag-type spaces over rings with a radical;
  - alternating quotients, if `H` has any (not checked).
- **Not covered, and still live (M1):** almost actions that are not Kazhdan cut-downs of genuine `H`-sets. There the
  Steinberg relations must fail on a vanishing but nonzero set of points.
- **Permanence caveat.** Alekseev–Bradford (arXiv:2601.18742, abstract only) prove closure of soficity under semidirect
  products with a "sofic C-action", and use it to build new examples, many of them halo products.
  - That operation is not in the list of `kazhdan-groups-in-sofic-permanence-closure-are-lef`, so the permanence
    firewall does not automatically cover it.
  - `G_Δ` is simple, so it is not itself a nontrivial semidirect product. Whether it sits inside one with a sofic
    action was not analyzed.

## Computation

`experiments/elementary-orbitwise-gap-2026-09-16/orbitwise_gap_check.py`, output in `output.txt` there, run
single-threaded under `timeout 600`.
- **Method.**
  - Exact ring and module tables, with all axioms checked.
  - `EL_n(𝒜)`-orbits on `W^n` from the generators, with invariance checked.
  - All `g ∈ M_n(𝒜)` when `|𝒜|^(n²)|V| ≤ 2·10^8`, otherwise sampled, plus 1500 random words.
- **Cases (17).**
  - `F_2`, `F_2[t]/(t²)`, `Z/4` and `𝒜 ⊕ 𝒜/(t)`, for `n = 2, 3`;
  - `F_2[t]/(t³)`, `F_2[x,y]/(x,y)²` and `T_2(F_2)` on its natural and regular modules;
  - a non-commutative 16-element ring.
- **Result.** The bound `1/(2n²)` holds everywhere. The observed minimum moved fraction is `1/2` (`T_2(F_2)`), and
  `2/3` or `4/7` for the commutative local rings.
- **Scope.** Evidence only. The theorem rests on the proof.

## Literature (2026-09-16)

- WebSearch budget was exhausted, so I queried the arXiv API export interface. Metadata was re-fetched for the ids
  below; abstracts only, nothing read at source.
- **Queries:**
  - `sofic AND Kazhdan`, `sofic AND "property (T)"`, `"linear sofic"`, `"locally embeddable" AND sofic`;
  - `"invariant random subgroups" AND sofic`, `"permutation stable" AND "property (T)"`;
  - `"fixed point ratio" AND "finite rings"`, `sofic AND Steinberg`.
- **Relevant hits:**
  - arXiv:2608.05362, Alekseev–Thom, *Centralizers of sofic approximations of Kazhdan groups*: ergodic centralizer
    forces LEF. Already on main as `kazhdan-ergodic-sofic-centralizer-forces-lef`.
  - arXiv:2511.16515, Alekseev–Drigalla, *Geometric property (T) for box spaces and sofic approximations*: every sofic
    approximation of a (T) group is approximately isomorphic to one with geometric (T).
  - arXiv:2601.18742, Alekseev–Bradford, *Sofic actions, halo products, and metric approximations of groups*:
    semidirect-product permanence.
  - arXiv:2603.16591, Salo, *Periodic points and residual finiteness of automorphism groups of subshifts*: LEF
    automorphism groups of block-gluing `Z²`-subshifts.
  - arXiv:2408.00110, Bowen–Chapman–Lubotzky–Vidick, *The Aldous–Lyons Conjecture I: Subgroup Tests*: non-co-sofic
    IRSs of free groups.
  - arXiv:2511.06586, Bowen–Chapman, *Surjunctivity does not characterize cosoficity of invariant random subgroups*.
  - arXiv:2508.15154, Manzoor, *Invariant Random Subgroups, Soficity, and Lück's determinant conjecture*.
  - arXiv:2602.05039, Bachner, *Linear sofic representations of amenable algebras*.
  - arXiv:1212.6780, Arzhantseva–Păunescu, *Linear sofic groups and algebras* (the linear-sofic-versus-sofic question).
- **Finding.** None of these abstracts states an orbitwise gap for elementary groups over rings with a radical, or
  exhibits a finitely generated sofic non-LEF Kazhdan group. This is not a full novelty audit.
- **Not read at source:** Ershov–Jaikin-Zapirain (imported through `elementary-groups-over-fg-rings-have-property-t`),
  Liebeck–Saxl, Caprace–Kassabov.

## What remains open

- `sofic-lamplighter-host-elementary-groups-are-sofic` at some `Δ = C(Γ)` with `Γ` not LEF, or any other sofic non-LEF
  envelope. A sofic approximation must be of type (M1) or (M2′).
- A cleaner negative target: prove that genuine finite `H`-sets of `H = EL_3(F_2⟨B⟩)` without a common orbitwise gap
  cannot have stabilizer IRSs converging to `δ_K` for a non-LEF quotient. That would leave only (M1).
- Whether the constant `1/2` holds in Theorem G for `g ∈ M_n(𝒜)`. It was observed in every computed case but not
  proved. For arbitrary additive `g` it fails (referee, below).

## Referee (2026-09-16)

**Verdict: landed with small fixes.** Theorem G is a correct, complete direct proof. Corollary C′, the host
consequence and the reduction route are sound. The target stays OPEN. Nothing was downgraded or withdrawn.

**What was checked.**
- **Theorem G, line by line** (route `elementary-group-column-actions-orbitwise-gap-proof`).
  - `P = ker(g − id)` is a subgroup. The `T_ij`-orbits are the cosets `x + (𝒜x_j)e_i`.
  - Coset lemma: `C ∩ P = p + (S ∩ P)`, which has index at least 2.
  - `|B_ij| ≤ 2|B_ij ∖ P| ≤ 2m`.
  - The swap `s_ij = e_ij(1)e_ji(−1)e_ij(1)` gives `(s_ij x)_i = x_j` and `(s_ij x)_j = −x_i`. I recomputed this from
    right to left. It uses unitality of `W`.
  - The union bound over `n(n−1) + n = n²` sets gives `|E| ≤ 2n²m < |O|`.
  - Conclusion: `O = Hx ⊆ L(x)^n ⊆ P`.
  - No hidden hypothesis: commutativity, semisimplicity and finiteness of `𝒜` are not used. `W` finite is used only
    through `|O| < ∞`.
- **Computation.**
  - Reran `experiments/elementary-orbitwise-gap-2026-09-16/orbitwise_gap_check.py`: the output is identical to
    `output.txt` (12 s).
  - Independent referee script, not landed: BFS and label-propagation orbits for `F_2`-algebras generated by random
    `3×3` and `4×4` matrices, with `n = 2, 3` and random fixed subspaces `P`. No violation of `1/(2n²)`.
- **Corollary C′, step 4.** I re-read `orbitwise-gap-sofic-approximations-local-embeddings-proof`, Corollary C steps
  1–5. It uses `ρ_N` only through the following: injective letters, invariant subsets, restriction of the gap to
  invariant subsets, the cutting lemma on a finite `H`-set, Theorem O, and Consequence 1. Linearity is not used. For
  the `F_2` host case, `X_N` is an `F_2`-space and C applies as stated. `ρ_N(H) = EL_n(φ_N(R))` holds because `φ_N` is
  onto its image.
- **Host consequence.**
  - `[Δ,Δ] ≤ EL_3(F_2[Δ])`: item 3 of `perfect-groups-embed-in-crossed-product-elementary-groups` with `X` a point,
    where `LC(pt,F_2) ⋊ Δ = F_2[Δ]`.
  - `F_2[Δ] ↪ R_Δ`: the crossed product is free over `LC` on the `u_ℓ`.
  - `EL_3 ≤ EL_n` by blocks, and LEF passes to subgroups.
  - Remark, not added to the node: by `group-ring-lef-iff-group-lef-iff-elementary-group-lef`, the `EL_3(F_2[Δ])`
    part holds under the weaker hypothesis "`Δ` not LEF".
- **Reduction route.**
  - The minimality and topological-freeness argument was re-derived: `h ∉ W ∪ δW ∪ supp λ`.
  - Finite generation of `R_Δ` and of `EL_3(R_Δ)`, and infiniteness, were checked.
  - The embedding `[L,L] ≤ EL_3(R_Δ)` was checked.
  - Every required node is committed and ESTABLISHED.
- **Discipline.**
  - The ids are at most 51 characters and match the filenames.
  - The new hole `sofic-lamplighter-host-elementary-groups-are-sofic` has `## Attempts`.
  - `bin/cairn search --similar` and keyword searches found no duplicate.
  - The target is not a root question with answer-route rules.
- **Citations.** Titles and authors of arXiv:2608.05362, 2511.16515, 2601.18742 and 2603.16591 were confirmed through
  the arXiv API. Abstracts of 2608.05362, 2511.16515 and 2601.18742 were fetched, and the notes' summaries of them are
  accurate. WebSearch budget was exhausted, so there was no broader current-status search. An arXiv author listing of
  A. Thom (fetched 2026-09-16) shows no sofic non-LEF simple Kazhdan group.

**What was changed.**
- *Constant `1/2`.* The solver's open question "does `1/2` hold in general" is false for arbitrary additive `g`.
  - Counterexample: `𝒜 = W = F_2 × F_2`, `n = 2`, the orbit of size 9 where both factors are nonzero, and
    `g = id + D∘C` whose fixed set is the hyperplane `{x_1 + y_1 = 0}`. It moves 4 of the 9 points. This was verified
    by script.
  - The question is now restricted to `g ∈ M_n(𝒜)` in the claim, the artifact §2 and these notes. Theorem G itself is
    unaffected.
- *Script docstring.* It pointed to a nonexistent id (`elementary-group-vector-models-have-orbitwise-gap`) and now
  points to `elementary-group-column-actions-have-orbitwise-gap`.
- *Caveat on the open claim.* Its Attempts now mention the Kun–Thom nonsofic generalized wreath products
  (arXiv:2608.06222, abstract read 2026-09-16). Whether that mechanism applies inside `EL_3(R_Δ)` was not analyzed.

**Scope, restated.**
- The obstruction covers only Kazhdan cut-downs of column models, meaning ring homomorphisms on entries.
- (M1), (M2′), affine, tensor and adjoint representations, and non-vector stabilizers stay open.
- The reduction adds no mathematics beyond the linear-sofic route with step 4 swapped. Its value is in naming the
  single missing input.
