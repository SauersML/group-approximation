import GroupApproximation.Analysis.NormalKazhdanUltraproduct
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure

/-!
# Sentence closure for the compression-criterion introduction

Exact row-numbered wrappers for census rows 38--48 and 50--51.  Row 49 is
intentionally absent: it is the separately audited printed corner Kazhdan
inequality, not a consequence to be replaced by the already formalized
moving-corner route.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

universe u v w

local instance sentence38QuotientCountable
    {G : Type} [Group G] [Countable G]
    (N : Subgroup G) [hN : N.Normal] : Countable (G ⧸ N) :=
  Function.Surjective.countable
    (@QuotientGroup.mk'_surjective G _ N hN)

/-- **Sentence 38.**  The quotient by a normal subgroup is MF exactly when
that subgroup is fixed by the printed MF-closure operator. -/
theorem manuscriptSentence38_quotientMF_iff_kernelIntersectionFixed
    (G : Type) [Group G] [Countable G]
    (N : Subgroup G) [N.Normal] :
    IsCDEOperatorMF (G ⧸ N) ↔ literalMFClosure G N = N :=
  isCDEOperatorMF_quotient_iff_literalMFClosure_eq N

/-- **Sentence 39.**  Membership in `Comp_G(L)` is exactly the displayed
one-sided conjugation inclusion. -/
theorem manuscriptSentence39_mem_compressionSet_iff
    {G : Type u} [Group G] (L : Subgroup G) (compressor : G) :
    compressor ∈ compressionSet L ↔
      ∀ ell ∈ L, compressor * ell * compressor⁻¹ ∈ L :=
  Iff.rfl

/-- **Sentence 40.**  The printed defect is exactly the ambient normal
closure of the displayed compression--centralizer commutators. -/
theorem manuscriptSentence40_printedDefect_display
    {G : Type u} [Group G] (L : Subgroup G) :
    printedDefect L = Subgroup.normalClosure
      {x | ∃ compressor : G,
        (∀ ell ∈ L, compressor * ell * compressor⁻¹ ∈ L) ∧
        ∃ centralizer : G,
          (∀ ell ∈ L, Commute centralizer ell) ∧
          ∃ ell ∈ L,
            x = ⁅compressor * centralizer * compressor⁻¹, ell⁆} :=
  rfl

/-- **Sentence 41.**  The defect is intrinsic to the pair `(G,L)`: equal
subgroups give equal defect subgroups, with no auxiliary choices. -/
theorem manuscriptSentence41_printedDefect_depends_only_on_pair
    {G : Type u} [Group G] {L₁ L₂ : Subgroup G} (hL : L₁ = L₂) :
    printedDefect L₁ = printedDefect L₂ :=
  congrArg printedDefect hL

/-- **Sentence 42.**  A normal Kazhdan subgroup contained in the printed
defect lies in the MF radical. -/
theorem manuscriptSentence42_normalKazhdan_defect_le_radical
    {G : Type} [Group G] [Countable G]
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (K : Subgroup G) [K.Normal]
    (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKD : K ≤ printedDefect L) :
    K ≤ manuscriptCoronaMFResidual G :=
  (manuscriptOneSidedCompressionCriterion G L hL).1 K hK hKD

/-- **Sentence 43.**  A nontrivial normal Kazhdan subgroup in the printed
defect obstructs MF-ness of the ambient group. -/
theorem manuscriptSentence43_nontrivial_defectKazhdan_obstructs_MF
    {G : Type} [Group G] [Countable G]
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (K : Subgroup G) [K.Normal]
    (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKD : K ≤ printedDefect L) (hKne : K ≠ ⊥) :
    ¬ IsCDEOperatorMF G :=
  (manuscriptOneSidedCompressionCriterion G L hL).2.1 K hK hKD hKne

/-- **Sentence 44.**  If the ambient group is Kazhdan and the printed defect
is all of it, then its MF radical is all of it. -/
theorem manuscriptSentence44_full_defect_gives_full_radical
    {G : Type} [Group G] [Countable G]
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (hG : HasKazhdanPropertyT.{0, 0} G)
    (hD : printedDefect L = ⊤) :
    manuscriptCoronaMFResidual G = ⊤ :=
  (manuscriptOneSidedCompressionCriterion G L hL).2.2 hG hD

/-- **Sentence 45.**  Every finite-dimensional linear representation over
every field kills the printed defect. -/
theorem manuscriptSentence45_finiteDimensional_representation_kills_defect
    {G : Type u} {k : Type v} {V : Type w}
    [Group G] [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (rho : G →* (V ≃ₗ[k] V))
    (L : Subgroup G) :
    printedDefect L ≤ rho.ker :=
  manuscriptPrintedDefectFiniteDimensionalSterility rho L

/-- **Sentence 46.**  Every displayed defect generator is invisible in
normalized Hilbert--Schmidt norm in every operator-norm asymptotic model. -/
theorem manuscriptSentence46_defectGenerator_HS_invisible :
    CompressionDefectHSInvisible :=
  manuscriptCompressionDefectHSInvisible

/-- **Sentence 47.**  The normality inclusion for the represented Kazhdan
subgroup makes its fixed-vector projection commute with the represented
ambient element. -/
theorem manuscriptSentence47_normality_makes_KazhdanProjection_commute
    {Gamma : Type u} {H : Type w} {B : Type v}
    [Group Gamma] [Group H] [CStarAlgebra B] [IsDedekindFiniteMonoid B]
    (D : UltraproductKazhdanProjection.KazhdanCompressionRep Gamma H B)
    (g : H)
    (hg : ∀ gamma : Gamma, ∃ delta : Gamma,
      g * D.iota gamma * g⁻¹ = D.iota delta) :
    ((D.pi g : unitary B) : B) * D.proj =
      D.proj * ((D.pi g : unitary B) : B) :=
  NormalKazhdanUltraproduct.nk_07_commute_proj D g hg

/-- **Sentence 48.**  A nonzero central corona projection yields the
polar-corrected complementary-corner asymptotic representation described in
the manuscript's central-corner lemma. -/
theorem manuscriptSentence48_central_complementary_corner :
    CentralCoronaCorner :=
  manuscriptCentralCoronaCorner

/-- **Sentence 50.**  The contradiction argument's unconditional endpoint
is the complete one-sided compression criterion.  This wrapper does not claim
the separately missing printed inequality of sentence 49. -/
theorem manuscriptSentence50_compressionCriterion_conclusion :
    CompleteOneSidedCompressionCriterion :=
  manuscriptCompleteOneSidedCompressionCriterion

/-- **Sentence 51.**  Independently of property `(T)`, the finite-dimensional
commutant calculation gives the corresponding statement over every field. -/
theorem manuscriptSentence51_finiteDimensional_commutant_route :
    FiniteDimensionalCommutantRigidity.{u, v, w} :=
  manuscriptFiniteDimensionalCommutantRigidity

end OneSidedMFRadical
end Manuscript
end GroupApproximation
