# Pestov 9.1 in Lean: adversarial review (lane pc-review), 2026-09-13, part 1

Part 1: statement fidelity and model tests of the endpoint vocabulary.
Part 2 (`pc-lean-review-2026-09-13-part2.md`): the landed modules, hidden hypotheses and axiom closures.
Part 3 (`pc-lean-review-2026-09-13-part3.md`): the fz surface under the coordinator's scope change. It covers the
bridges, the discharge tracker for the binder-free endpoint, new landings, drafts in flight, gates and CI.

Reviewed against origin/main at 2f124d801 (02:06 CDT). Every file on main under `GroupApproximation/Pestov91/`
and every `Palomar/Pestov91*` file was landed by the parallel **fz** campaign (session 6dbfc571, lanes `p91-*`), not by
a pc lane. Their probe records live in `.../6dbfc571-.../scratchpad/fz/lanes/p91-*.green.*`. At review time no
`$PC/lanes/*.green.*` record exists, and `pcprobe.sh`/`pcland.sh` have not been announced.

## 1. Open Question 9.1, verbatim

Source: arXiv:0804.3968v8, fetched on MSI. I read page 21 directly from the PDF (Section 9, "Some classes of groups
to look at"):

> **Open question 9.1** (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it be
> hyperlinear (sofic)?

Reading: a positive answer exhibits one group that is infinite, simple, Kazhdan and hyperlinear. The parenthetical
asks the same with "sofic", which is the stronger form (Theorem 3.3, Elek–Szabó: sofic ⇒ hyperlinear). The quotation
in the docstring of `Palomar/Pestov91Challenge.lean` matches the PDF word for word, including "(Cf. Ozawa [64])".

The survey's own definitions, read from pages 5–9 of the same PDF:
- Example 2.3 (p. 5): `d_hamm(σ,τ) = (1/n)·#{i : σ(i) ≠ τ(i)}` on `S_n`.
- Example 2.7 (p. 6): `d_HS(u,v) = ‖u − v‖₂ = sqrt((1/n)·Σ_{i,j} |u_ij − v_ij|²)` on `U(n)`, normalized so that
  `‖I‖₂ = 1`.
- Definitions 3.1 and 3.2 (p. 6): `G` is sofic (hyperlinear) if it is isomorphic to a subgroup of a metric
  ultraproduct of `(S_n, d_hamm)` (resp. `(U(n), d_HS)`).
- Theorem 3.5 (p. 8): `G` is sofic iff for every finite `F` and `ε > 0` there are `n` and `θ : F → S_n` with
  - (1) `g, h, gh ∈ F ⇒ d_hamm(θ(g)θ(h), θ(gh)) < ε`;
  - (2) `e ∈ F ⇒ d(θ(e), Id) < ε`;
  - (3) distinct `x, y ∈ F ⇒ d_hamm(θ(x), θ(y)) ≥ 1/4`.
- Theorem 3.6 (p. 9) states the same with `U(n)` and `‖·‖₂`. Remark 3.7 says (3) can be sharpened to any constant
  below `√2`.
- Page 9: "an apparent greater generality of allowing uncountable groups is an illusion"; both notions are local.
  Question 9.1 imposes no countability.

## 2. The vocabulary the endpoint uses

There are two vocabularies on main, with bridges between them.
- **Palomar shared block** (`Palomar/Pestov91Challenge.lean`, landed by fz `p91-palomar` in b490bf08d, blob md5
  `ba2518e9…`):
  - `IsKazhdanPair` and `HasPropertyT`, over complex Hilbert spaces;
  - `FiniteCarrier`, `hammingDist` and `IsSoficGroup`;
  - `hsDistSq` and `IsHyperlinearGroup`;
  - `Infinite` and `IsSimpleGroup`, taken from Mathlib.
- **Development:**
  - `HasKazhdanPropertyT` (real Hilbert spaces, `Kazhdan/Kazhdan.lean:33`);
  - `HasKazhdanPropertyTComplex` (`Kazhdan/KazhdanComplex.lean:97`);
  - `IsSofic` (`Sofic/Sofic.lean:183`);
  - `IsHyperlinear` (`Sofic/Hyperlinear.lean:154`);
  - `IsLEF` (`Sofic/LEF.lean:50`).
- **Bridges** in `Palomar/Pestov91Solution.lean`:
  - `hasPropertyT_iff_hasKazhdanPropertyT`. This is `HasPropertyT G ↔ HasKazhdanPropertyT.{0,0} G`, through
    `hasKazhdanPropertyT_iff_complex` (`KazhdanComplex.lean:149`: realification one way, complexification the other).
  - `isSoficGroup_of_isSofic` and its converse, and `isHyperlinearGroup_of_isHyperlinear` and its converse. These
    only repackage the carrier.
  - The block bodies are the development bodies field for field, and the bridge proofs are term-mode repackagings.

### 2.1 Property (T): faithful

- **Block.** `∃ Q ε, 0 < ε ∧ ∀ (E : Type)` complete complex inner-product space, `∀ ρ : G →* (E ≃ₗᵢ[ℂ] E)`,
  `∀ x` with `‖x‖ = 1`, `(∀ q ∈ Q, ‖ρ q x − x‖ < ε) → ∃ y ≠ 0, ∀ g, ρ g y = y`.
- **Literature.** This is Bekka–de la Harpe–Valette Definition 1.1.3 for a discrete group (a compact set is a finite
  set). Mathlib's group structure on `E ≃ₗᵢ[ℂ] E` composes as functions, so `ρ` is a genuine representation.
- **Checked at the source,** in the book PDF hosted on Bekka's homepage (`KazhdanTotal.pdf`), pp. 31–34. I did not
  compare with the printed Cambridge edition.
  - §1.1 fixes "Hilbert spaces are always complex".
  - Definition 1.1.1(i): ξ is (Q, ε)-invariant when `sup_{x∈Q} ‖π(x)ξ − ξ‖ < ε‖ξ‖`.
  - Definition 1.1.3: (Q, ε) is a Kazhdan pair when every unitary representation with a (Q, ε)-invariant vector has a
    nonzero invariant vector, and G has (T) when it "has a *compact* Kazhdan set".
  - Why the block's form agrees:
    - for finite `Q` the supremum is a maximum;
    - by homogeneity every nonzero ξ rescales to a unit vector;
    - the strict inequality excludes ξ = 0;
    - for discrete groups strong continuity is automatic.
- **Positive control, finite groups.** `hasKazhdanPropertyT_of_finite : ∀ (G : Type u) [Group G] [Finite G],
  HasKazhdanPropertyT.{u, v} G` (`Sofic/NormalKazhdanMFRadical.lean:30`), with `Q = univ` and `ε = 1`.
  - The orbit sum of an almost invariant unit vector is nonzero and invariant.
  - In the block's vocabulary the fz driver `Palomar/Pestov91Driver.lean` (probe 0913-020136-50440, not landed) checks
    `HasPropertyT PUnit`.
- **Negative controls, ℤ does not.**
  - `not_hasKazhdanPropertyT_multiplicative_int : ¬ HasKazhdanPropertyT.{0, 0} (Multiplicative ℤ)`
    (`Kazhdan/IntegerNotKazhdan.lean:39`).
  - Free groups: `not_hasKazhdanPropertyT_freeGroup` (`Kazhdan/FreeGroupSharpProfile.lean:67`).
  - Amenable groups with (T) are finite (`Kazhdan/AmenableKazhdanFinite.lean:105`).
- **Gap at 02:06, since closed.** The fz Palomar driver has positive controls only, and a `HasPropertyT` that
  unfolded to `True` would pass them. fz p91-statement has since compiled `test_not_hasPropertyT_int` and
  `test_not_isKazhdanPair_int` in the block's vocabulary (record 0913-021315-6428, landed under
  `wip/pestov91/fidelity/`; part 2 §6.11).
- **Universes: no trivialization.**
  - `E` ranges over `Type`, and the witness is a group in `Type`, so `ℓ²(G)` is among the tested spaces.
  - `IsKazhdanPair.liftUniverse` (`Kazhdan/KazhdanUniverse.lean:335`) proves that a pair tested on spaces in the
    group's universe is a pair in every universe: the cyclic subrepresentation is a GNS representation built from the
    group. `lowerUniverse` and `HasKazhdanPropertyT.of_max` give the converse.
  - A vacuous (T) would need a universe with no nonzero Hilbert space, and none exists (`ULift ℂ`). A (T) that is too
    easy would need too few spaces, and liftUniverse rules that out.

### 2.2 Soficity: faithful, and the direction that matters is elementary

- **Block.** `∀ F ε, 0 < ε → ∃` a nonempty finite `Y` and `σ : G → Perm Y` with
  - `hammingDist(σ(gh), σg·σh) ≤ ε` for **all** `g, h ∈ F`;
  - `1 − ε ≤ hammingDist(σg, σh)` for `g ≠ h` in `F`.
  - The body is byte-identical to the Bowen–Chapman Challenge block and field-identical to `SoficModel`.
- **Block ⇒ Theorem 3.5.** This is the direction an existence theorem needs: a stronger definition is safe.
  - (1) The block asks for ≤ on more pairs. Use `ε/2` to get the strict inequality.
  - (3) `1 − ε ≥ 1/4` once `ε ≤ 3/4`.
  - (2) Take (1) at `(e, e)`: `d(σe, σe·σe) = d(Id, σe)` by left invariance (`hammingDistance_left_invariant`,
    `Sofic/Sofic.lean`).
  - `BowenChapman.isPestovSofic_of_isSoficGroup` proves (1) and (3) in Lean, and `isSoficGroup_of_isPestovSofic` the
    converse by amplification. Both are in `wip/bowen-chapman/fidelity/BcxPestovEquivalence.lean`, an unwired WIP
    file whose header reports a green compile on 09-12. I did not re-verify it, and the direction needed here does
    not depend on it.
- **Positive controls.**
  - `isSofic_freeGroup (α : Type*) : IsSofic (FreeGroup α)` (`Sofic/FreeGroupResiduallyFinite.lean:375`).
  - `isSofic_of_finite` (`Sofic/SoficPositiveControl.lean:99`).
- **Not vacuous.**
  - `GroupApproximation.BowenChapman.exists_fg_surjunctive_not_isSofic : ∃ (E : Type) (_ : Group E), Group.FG E ∧
    Surjunctivity.IsSurjunctive E ∧ ¬ IsSofic E` (`BowenChapman/Endpoint.lean:54`). So `¬ ∀ G, IsSofic G` is a theorem
    of main.
  - The degenerate control `soficSeparation_fails_of_eq` is in the fz probe-only
    `LEFHyperlinearChallengeDriver` (0913-013243-89830).
  - The block-vocabulary composition `∃ G, ¬ Pestov91.IsSoficGroup G` compiled in the pc-review probe with closure
    `[propext, Classical.choice, Quot.sound]`. That probe failed on another test, so this is not landing evidence
    (§3).

### 2.3 Hyperlinearity: faithful, normalized Hilbert–Schmidt metric

- **Block.**
  - `σ : G → Matrix Y Y ℂ` with every `σ g` in `Matrix.unitaryGroup Y ℂ`.
  - `hsDistSq(σ(gh), σg·σh) ≤ ε` for `g, h ∈ F`.
  - `2 − ε ≤ hsDistSq(σg, σh)` for `g ≠ h` in `F`.
  - `hsDistSq Y A B = (Σ_i Σ_j normSq(A_ij − B_ij)) / |Y|`.
- **The metric.** `hsDistSq` is exactly `d_HS²` of Example 2.7. It is the normalized Hilbert–Schmidt metric, not the
  operator norm. For example, `I` and `diag(−1, 1, …, 1)` on `n` points are at operator distance 2 but squared HS
  distance `4/n`. My Lean check of this computation did not compile (§3), so the point rests on the formula.
- **Block ⇒ Theorem 3.6.**
  - (1) `d_HS ≤ √ε`.
  - (3) `d_HS ≥ √(2 − ε) ≥ 1/4` for `ε ≤ 1`.
  - (2) Take (1) at `(e, e)`, using left invariance of `d_HS` under unitaries.
  - The block's `2 − ε` is Remark 3.7's `√2`.
  - Pestov's Theorem 3.3 computes `d_hamm = ½·d_HS²` on permutation matrices, which is `permMatrix_hsDistSq`
    (`Sofic/Hyperlinear.lean`).
- **Controls.**
  - Positive: `isHyperlinear_of_finite` and `isHyperlinear_of_isSofic` (`Sofic/Hyperlinear.lean:175`).
  - Degenerate: `hyperlinearSeparation_fails_of_eq` (fz probe-only driver).
  - No group is known not to be hyperlinear (Pestov, Question 3.9), so a strong non-vacuity test is not available. It
    is not needed for the endpoint, whose risk is a definition that is too weak. Here the block is visibly at least
    as strong as Theorem 3.6.

### 2.4 Simplicity and infiniteness: Mathlib, checked at the pinned revision

The manifest pins Mathlib to v4.32.0, whose source is rev 81a5d257 in the local clone:
- `class IsSimpleGroup : Prop extends Nontrivial G where eq_bot_or_eq_top_of_normal : ∀ H : Subgroup G, H.Normal →
  H = ⊥ ∨ H = ⊤` (`Mathlib/GroupTheory/Subgroup/Simple.lean:38`). `Nontrivial` excludes the trivial group, so this
  is the textbook notion.
- `class Infinite (α : Sort*) : Prop where not_finite : ¬Finite α` (`Mathlib/Data/Finite/Defs.lean:134`). `Unit` is
  finite, so it is not `Infinite`.

### 2.5 The Challenge statements: faithful, binder-free

- `Pestov91.exists_infinite_simple_propertyT_hyperlinear : ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G
  ∧ HasPropertyT G ∧ IsHyperlinearGroup G`.
- `Pestov91.exists_infinite_simple_propertyT_sofic` is the same with `IsSoficGroup`.
- Neither has a hypothesis. `comparator-pestov91.json` permits exactly `[propext, Quot.sound, Classical.choice]`.
- An existential in `Type` is the strongest universe placement.

**Verdict of part 1.** The endpoint vocabulary means what the literature means. Every definition is at least as
strong as Pestov's local form, and no universe trivializes anything. The one missing model test is a *compiled*
negative control in the Challenge vocabulary.

## 3. pc-review driver (probe-only, not for landing)

`$PC/lanes/pc-review/Palomar/Pestov91ReviewModelTests.lean`, with a probe-only `lakefile.toml` overlay. I trimmed it to
the controls that fz's compiled `wip/pestov91/fidelity/Pestov91ModelTests.lean` does not state (part 2 §6.11):
- `IsSoficGroup (FreeGroup (Fin 2))`;
- `∃ G, ¬ IsSoficGroup G`;
- `¬ Infinite Unit`;
- the HS computation of §2.3.

Outcome: probe `0913-022448-59655` (base 1d4068771) **FAILED**, on the HS test only. After `simp`, the sum ran over
the carrier's bundled `Fintype` instance, and `Fin.sum_univ_four` did not fire, leaving an unsolved goal.
- The other three compiled. Their printed closures were `[propext, Classical.choice, Quot.sound]`.
- Because the probe failed overall, this is **not** landing evidence, and pcprobe left no `.green.` record.
- A fixed version (two points, with `show` to normalize the sum) is in the lane directory. It was not re-probed: the
  coordinator stopped the PC swarm at 02:30 as a duplicate of the fz swarm (c052afa7d).
- The fidelity conclusions of §2 do not rest on this driver.
