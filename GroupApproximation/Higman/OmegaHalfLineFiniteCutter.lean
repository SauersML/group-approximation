import GroupApproximation.Higman.OmegaHalfLineGraphGate
import GroupApproximation.Higman.PairedReturnCutter
import GroupApproximation.Higman.RowDeletionBenign
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Set

/-!
# Finite-cutter coordinates for the one-sided Omega edge

The infinite-basis edge in `OmegaHalfLineGraphGate` is the semantic model, not
a finitely presented construction.  This file begins its finite compression.
The right-tail labels form a decidable infinite and co-infinite subset of
Higman's countable conjugator alphabet.  We choose an alphabet equivalence
with `Z` carrying that subset *exactly* to the nonnegative half-line.  After
applying `FreeGroup.freeGroupCongr`, Row's literal three-generator `LSub`
therefore becomes an exact finite cutter for the label gate.  This is the
row-marker half that will be equalized with the paired-return five-cutter.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The subset of the conjugator alphabet consisting of canonical right-tail
sequence words. -/
noncomputable def rightTailLabel (m : ℕ) : Set ↥Conj.K :=
  bK '' rightTailSeq m

/-- An explicit infinite family of right-tail labels. -/
noncomputable def rightTailLabelNat (m n : ℕ) : ↥(rightTailLabel m) :=
  ⟨bK (Finsupp.single (m : ℤ) ((n : ℤ) + 1)), by
    refine ⟨Finsupp.single (m : ℤ) ((n : ℤ) + 1), ?_, rfl⟩
    intro i hi
    have him : i = (m : ℤ) := by
      by_contra him
      exact hi (by simp [him])
    omega⟩

theorem rightTailLabelNat_injective (m : ℕ) :
    Function.Injective (rightTailLabelNat m) := by
  intro n k hnk
  have hb : bK (Finsupp.single (m : ℤ) ((n : ℤ) + 1)) =
      bK (Finsupp.single (m : ℤ) ((k : ℤ) + 1)) :=
    congrArg Subtype.val hnk
  have hs := bK_injective hb
  have hv := congrArg (fun f : E => f (m : ℤ)) hs
  simp only [Finsupp.single_eq_same] at hv
  omega

noncomputable instance rightTailLabel_infinite (m : ℕ) :
    Infinite ↥(rightTailLabel m) :=
  Infinite.of_injective (rightTailLabelNat m)
    (rightTailLabelNat_injective m)

/-- An explicit infinite family outside the right-tail labels, supported at
the coordinate immediately to the left of the cutoff. -/
noncomputable def outsideRightTailLabelNat (m n : ℕ) :
    ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) :=
  ⟨bK (Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1)), by
    rintro ⟨l, hl, heq⟩
    have hseq : l = Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1) :=
      bK_injective heq
    have hnz : ((n : ℤ) + 1) ≠ 0 := by omega
    have := hl ((m : ℤ) - 1) (by simpa [hseq] using hnz)
    omega⟩

theorem outsideRightTailLabelNat_injective (m : ℕ) :
    Function.Injective (outsideRightTailLabelNat m) := by
  intro n k hnk
  have hb : bK (Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1)) =
      bK (Finsupp.single ((m : ℤ) - 1) ((k : ℤ) + 1)) :=
    congrArg Subtype.val hnk
  have hs := bK_injective hb
  have hv := congrArg (fun f : E => f ((m : ℤ) - 1)) hs
  simp only [Finsupp.single_eq_same] at hv
  omega

noncomputable instance outsideRightTailLabel_infinite (m : ℕ) :
    Infinite ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) :=
  Infinite.of_injective (outsideRightTailLabelNat m)
    (outsideRightTailLabelNat_injective m)

/-- A denumeration of the right-tail part of the label alphabet. -/
@[implicit_reducible] noncomputable def rightTailLabelDenumerable (m : ℕ) :
    Denumerable ↥(rightTailLabel m) :=
  Classical.choice (nonempty_denumerable ↥(rightTailLabel m))

/-- A denumeration of the complementary part of the label alphabet. -/
@[implicit_reducible] noncomputable def outsideRightTailLabelDenumerable (m : ℕ) :
    Denumerable ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) :=
  Classical.choice
    (nonempty_denumerable
      ↥((rightTailLabel m)ᶜ : Set ↥Conj.K))

/-- A label enumeration adapted to the gate: right-tail labels receive
nonnegative integers and every other label receives a negative integer. -/
noncomputable def rightTailLabelEquivInt (m : ℕ) : ↥Conj.K ≃ ℤ := by
  classical
  letI : Denumerable ↥(rightTailLabel m) := rightTailLabelDenumerable m
  letI : Denumerable ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) :=
    outsideRightTailLabelDenumerable m
  exact (Equiv.Set.sumCompl (rightTailLabel m)).symm |>.trans
    ((Denumerable.eqv _).sumCongr (Denumerable.eqv _)) |>.trans
    Equiv.intEquivNatSumNat.symm

/-- The adapted enumeration recognizes the right-tail label set exactly by
the sign of the resulting row index. -/
theorem rightTailLabelEquivInt_nonneg_iff (m : ℕ) (q : ↥Conj.K) :
    0 ≤ rightTailLabelEquivInt m q ↔ q ∈ rightTailLabel m := by
  classical
  letI : Denumerable ↥(rightTailLabel m) := rightTailLabelDenumerable m
  letI : Denumerable ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) :=
    outsideRightTailLabelDenumerable m
  by_cases hq : q ∈ rightTailLabel m
  · simp only [rightTailLabelEquivInt, Equiv.trans_apply,
      Equiv.Set.sumCompl_symm_apply_of_mem hq, Equiv.sumCongr_apply]
    constructor
    · intro
      exact hq
    · intro
      change 0 ≤ Int.ofNat _
      exact Int.natCast_nonneg _
  · simp only [rightTailLabelEquivInt, Equiv.trans_apply,
      Equiv.Set.sumCompl_symm_apply_of_notMem hq, Equiv.sumCongr_apply]
    constructor
    · intro hnonneg
      change 0 ≤ Int.negSucc _ at hnonneg
      omega
    · exact False.elim ∘ hq

/-- Reindex the free conjugator alphabet by the adapted integer row. -/
noncomputable def rightTailFreeEquiv (m : ℕ) :
    FreeGroup ↥Conj.K ≃* FreeGroup ℤ :=
  FreeGroup.freeGroupCongr (rightTailLabelEquivInt m)

@[simp] theorem rightTailFreeEquiv_of (m : ℕ) (q : ↥Conj.K) :
    rightTailFreeEquiv m (FreeGroup.of q) =
      FreeGroup.of (rightTailLabelEquivInt m q) := rfl

/-- The adapted alphabet followed by Higman's row-basis embedding. -/
noncomputable def rightTailRowHom (m : ℕ) :
    FreeGroup ↥Conj.K →* Row.F₀ :=
  Row.basisHom.comp (rightTailFreeEquiv m).toMonoidHom

theorem rightTailRowHom_injective (m : ℕ) :
    Function.Injective (rightTailRowHom m) :=
  Row.basisHom_injective.comp (rightTailFreeEquiv m).injective

@[simp] theorem rightTailRowHom_of (m : ℕ) (q : ↥Conj.K) :
    rightTailRowHom m (FreeGroup.of q) =
      Row.row (rightTailLabelEquivInt m q) := by
  rw [rightTailRowHom, MonoidHom.comp_apply]
  change Row.basisHom (rightTailFreeEquiv m (FreeGroup.of q)) = _
  rw [rightTailFreeEquiv_of, Row.basisHom_of]

/-- The label-coordinate subgroup is carried *exactly* to the nonnegative
half row.  This is the semantic equalizer equation behind the finite
row-marker cutter. -/
theorem map_rightTailCoord_rightTailRowHom (m : ℕ) :
    (Star.coordSub (rightTailLabel m)).map (rightTailRowHom m) =
      Row.HalfRow := by
  unfold Star.coordSub
  rw [MonoidHom.map_closure, Row.halfRow_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨rightTailLabelEquivInt m q,
      (rightTailLabelEquivInt_nonneg_iff m q).mpr hq,
      (rightTailRowHom_of m q).symm⟩
  · rintro ⟨i, hi, rfl⟩
    let q : ↥Conj.K := (rightTailLabelEquivInt m).symm i
    have hq : q ∈ rightTailLabel m :=
      (rightTailLabelEquivInt_nonneg_iff m q).mp (by
        simpa [q] using hi)
    exact ⟨FreeGroup.of q, ⟨q, hq, rfl⟩, by
      simp [q]⟩

/-- The adapted row map itself is a torsion-free finitely presented overgroup
of the countable free label group. -/
noncomputable def rightTailLabelOvergroup (m : ℕ) :
    TorsionFreeFPOvergroup (FreeGroup ↥Conj.K) where
  K := Row.F₀
  torsionFree := IsPowerTorsionFree.of_isMulTorsionFree
  emb := rightTailRowHom m
  emb_injective := rightTailRowHom_injective m

/-- **Finite row-marker witness.**  The restricted label-coordinate subgroup
is benign.  Its cutter is ultimately Row's literal `LSub = <b,t0,t1>`; the
only new work here is the exact adapted-alphabet comap. -/
theorem benignTF_rightTailCoord (m : ℕ) :
    BenignTF (Star.coordSub (rightTailLabel m)) := by
  have h := BenignTF.comap (rightTailLabelOvergroup m)
    (rightTailRowHom m) Row.benignTF_halfRow
  have hcomap : Row.HalfRow.comap (rightTailRowHom m) =
      Star.coordSub (rightTailLabel m) := by
    rw [← map_rightTailCoord_rightTailRowHom m]
    exact Subgroup.comap_map_eq_self_of_injective
      (rightTailRowHom_injective m) _
  rwa [hcomap] at h

/-! ## Equalizing the five-cutter with the row marker -/

/-- The paired-return ambient, viewed as an overgroup of the free graph
alphabet.  Its literal five-cutter cuts out the whole alphabet: every word is
sent through `Star.graphHom`, hence lands in `Star.graphSub` before the exact
five-cutter comap is applied. -/
noncomputable def pairedGraphTopWitness :
    TorsionFreeBenignWitness (⊤ : Subgroup (FreeGroup ↥Conj.K)) := by
  letI : Group.IsFinitelyPresented PairedReturnCutter.Ambient :=
    PairedReturnCutter.ambient_finitelyPresented
  exact
    { witness :=
        { K := PairedReturnCutter.Ambient
          emb := (MatchedSubgroupAmalgam.bigInA
            PairedReturnCutter.edgeToP PairedReturnCutter.edgeToC).comp
              Star.graphHom
          emb_injective :=
            (Amalgam.of_injective_push PairedReturnCutter.edgeToP
              PairedReturnCutter.edgeToC
              PairedReturnCutter.edgeToP_injective
              PairedReturnCutter.edgeToC_injective false).comp
                Star.graphHom_injective
          L := PairedReturnCutter.fiveCutter
          L_fg := PairedReturnCutter.fiveCutter_fg
          comap_eq := by
            change (PairedReturnCutter.fiveCutter.comap
              (MatchedSubgroupAmalgam.bigInA
                PairedReturnCutter.edgeToP
                PairedReturnCutter.edgeToC)).comap Star.graphHom = ⊤
            rw [PairedReturnCutter.fiveCutter_comap_left]
            ext w
            simp only [Subgroup.mem_comap, Subgroup.mem_top, iff_true]
            exact Star.mem_graphSub.mpr ⟨w, rfl⟩ }
      torsionFree := PairedReturnCutter.ambient_torsionFree }

/-- A chosen concrete row-marker witness.  Its existence is the exact
`map/rightTailRowHom = HalfRow` calculation above combined with Row's
three-generator central-HNN cutter. -/
noncomputable def rightTailCoordWitness (m : ℕ) :
    TorsionFreeBenignWitness (Star.coordSub (rightTailLabel m)) :=
  Classical.choice (benignTF_rightTailCoord m)

/-- The unreduced direct-product witness.  Naming it separately keeps its
literal product ambient visible to subsequent projection calculations. -/
noncomputable def rightTailPairedProductWitnessRaw (m : ℕ) :
    TorsionFreeBenignWitness
      ((⊤ : Subgroup (FreeGroup ↥Conj.K)) ⊓
        Star.coordSub (rightTailLabel m)) :=
  pairedGraphTopWitness.inf (rightTailCoordWitness m)

/-- **Five-cutter/Row equalizer.**  The direct-product witness pairs the
paired-return graph coordinate with the adapted row marker.  Its cutting
subgroup is finitely generated (the five-cutter on the first side and Row's
finite cutter, through the chosen comap witness, on the second), while its
comap is exactly the right-tail coordinate subgroup. -/
noncomputable def rightTailPairedEqualizerWitness (m : ℕ) :
    TorsionFreeBenignWitness (Star.coordSub (rightTailLabel m)) := by
  have u := rightTailPairedProductWitnessRaw m
  simpa only [top_inf_eq] using u

/-- The first coordinate of the equalizer embedding is literally the
paired-return embedding of the conjugator graph word.  Thus no semantic graph
information is lost by the finite row compression. -/
theorem rightTailPairedProductWitnessRaw_fst_emb (m : ℕ)
    (w : FreeGroup ↥Conj.K) :
    ((rightTailPairedProductWitnessRaw m).witness.emb w).1 =
      MatchedSubgroupAmalgam.bigInA PairedReturnCutter.edgeToP
        PairedReturnCutter.edgeToC (Star.graphHom w) := rfl

end Omega
end Higman
end GroupApproximation
