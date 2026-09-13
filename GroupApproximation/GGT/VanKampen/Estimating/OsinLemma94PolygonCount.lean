import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCovers
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94RegionSideCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The count piece of Osin's Lemma 9.4: the covers half, and the side budget as the residual

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs
of type (A1) in `∂Δ_i`, `i = 1, …, d`.  Assume that `S ≥ n √ρ`.  Then `S_i ≥ n_i √ρ / 60` for
some `i`.  Indeed otherwise we have `S = ∑_{i=1}^d S_i ≤ (√ρ / 60) ∑_{i=1}^d n_i < n √ρ`."

`OsinLemma94PolygonCountInput` (in `OsinLemma94PlanarPieces.lean`) is the side budget `K`
together with the covering `S ≤ ∑ S_i + L n`.  This module proves the covering for every `ε`
with `L = 24 ε` (`osinLemma94PolygonCoversInput`), given that no unbound dart has its own cell
across (`OsinLemma94UnboundSameCellStatement`).  It reduces the count piece to the side budget
and that statement (`osinLemma94PolygonCountInput_of_sideBudget`).

The covering combines two bounds.
* An unbound dart facing no selected region and not its own cell lies across an (A1) side of a
  polygon
  (`OsinLemma94RealizedPolygons.covers_of_regionFacing_le`, in `OsinLemma94PolygonCovers.lean`).
* The unbound darts facing a selected region number at most `2 ε |M|`
  (`RealizedSectionFamily.sum_card_regionFacingUnbound_le`, in `OsinLemma94RegionSideCount.lean`).
  Here `|M| ≤ 3 (n + count - 1) ≤ 12 n`, since there are at most four sections and `n ≥ 1`.

The relator words have length at least `ρ ≥ ⌈c / λ⌉ + 2`, so none of them has value one and
every relator cell has at least two darts.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

/-- **Covering half of the count piece of Lemma 9.4.**  "`S = ∑_{i=1}^d S_i`": the unbound
darts are covered by the (A1) sides of the polygons up to a slack `L n`, with `L` chosen after
`ε`. -/
def OsinLemma94PolygonCoversInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ eps : ℕ,
        ∃ L : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal → P.Covers L

/-- **No unbound dart has its own cell across.**  At the parameters of Lemma 9.4, for `ρ` large,
no unbound dart of a relator cell of the optimal diagram has its reverse on the same cell.  The
covering half uses it there: doubling such an edge gives a region from a cell to itself, which
is not a candidate (`RespectsSections`), so maximality gives no contradiction. -/
def OsinLemma94UnboundSameCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ eps : ℕ,
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
                    d ∈ RegionCandidate.unboundDarts S.family i →
                      (cell S.diagram i).face ≠
                        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)

/-- **The covering half holds with `L = 24 ε` and `ρ₀ = max (⌈c / λ⌉ + 2) ρ₁`**, given that no
unbound dart has its own cell across, where `ρ₁` is the threshold of that statement. -/
theorem osinLemma94PolygonCoversInput (hsame : OsinLemma94UnboundSameCellStatement.{u, w, v}) :
    OsinLemma94PolygonCoversInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  obtain ⟨rho1, -, hsame1⟩ := hsame D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  refine ⟨24 * eps, max (⌈c / lambda⌉₊ + 2) rho1, lt_max_of_lt_left (by omega),
    fun rho hrho W hW Delta cuts hleast hcells S hcard hmin P _ => ?_⟩
  have hrho2 : ⌈c / lambda⌉₊ + 2 ≤ rho := (max_le_iff.mp hrho).1
  have hrhoc : c < lambda * rho := by
    have hceil : c / lambda ≤ ⌈c / lambda⌉₊ := Nat.le_ceil _
    have hcast : ((⌈c / lambda⌉₊ : ℕ) : ℝ) + 1 ≤ rho := by
      exact_mod_cast (by omega : ⌈c / lambda⌉₊ + 1 ≤ rho)
    have hlt : c < rho * lambda := (div_lt_iff₀ hlambda).mp (by linarith)
    linarith [mul_comm lambda (rho : ℝ)]
  have hvalue := S.cell_listVal_ne_one hW hlambda hrhoc
  refine P.covers_of_regionFacing_le hvalue (S.one_lt_cellDarts_length hW (by omega))
    (hsame1 rho (max_le_iff.mp hrho).2 W hW Delta cuts hleast hcells S hcard hmin) (24 * eps) ?_
  have hfam : S.family.card ≤ 12 * Delta.rCellCount := by
    have := cuts.count_le
    omega
  calc _ ≤ 2 * eps * S.family.card :=
        S.toRealizedSectionFamily.sum_card_regionFacingUnbound_le hvalue
    _ ≤ 2 * eps * (12 * Delta.rCellCount) := Nat.mul_le_mul le_rfl hfam
    _ = 24 * eps * Delta.rCellCount := by ring

/-- **Side budget half of the count piece of Lemma 9.4.**  Lemma 9.3, "`∑ n_i ≤ 53 n`", and
(38), "`k_i ≤ 4 n_i`": the polygons have at most `K n` sides in total, with `K` chosen after
`ε`.

Model test: summed over every polygon, as here, this is over-strong.  A `G`-face whose walk
reads a value-one subword of `∂Δ`, such as a bubble on a spur of a section, is a polygon with
no (A1) side, and there can be arbitrarily many of them with `n = 1`. -/
def OsinLemma94PolygonSideBudgetInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal → P.SideBudget K

/-- **The count piece of Lemma 9.4 follows from the side budget**, given that no unbound dart has
its own cell across.  The covering half is `osinLemma94PolygonCoversInput`. -/
theorem osinLemma94PolygonCountInput_of_sideBudget
    (hbudget : OsinLemma94PolygonSideBudgetInput.{u, w, v})
    (hsame : OsinLemma94UnboundSameCellStatement.{u, w, v}) :
    OsinLemma94PolygonCountInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, hK⟩ := hbudget D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨K, rho1, hrho1, hKeps⟩ := hK eps heps
  obtain ⟨L, rho2, _, hL⟩ := osinLemma94PolygonCoversInput.{u, w, v} hsame D hhyper lambda c mu
    hlambda hlambda1 hc hmu hmu16 eps
  refine ⟨K, L, max rho1 rho2, lt_of_lt_of_le hrho1 (le_max_left _ _),
    fun rho hrho W hW Delta cuts hleast hcells S hcard hmin P hmax => ⟨?_, ?_⟩⟩
  · exact hKeps rho (max_le_iff.mp hrho).1 W hW Delta cuts hleast hcells S hcard hmin P hmax
  · exact hL rho (max_le_iff.mp hrho).2 W hW Delta cuts hleast hcells S hcard hmin P hmax

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonCoversInput
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonCountInput_of_sideBudget

end GroupApproximation.GGT.VanKampen
