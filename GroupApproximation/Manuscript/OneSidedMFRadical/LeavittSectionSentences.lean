import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedLeavittEquations
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceDefectCalculationProofClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Leavitt.RankTwelveCorner
import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Leavitt.ElementaryGroup

/-!
Historical scope: this module records the earlier rank-twelve presentation.
The current manuscript proves the same headline through the general
full-complementary-idempotent criterion; the declarations below are unchanged.

# `non_mf_groups_exist.tex`, section "The binary Leavitt group": sentence-level closure

`non_mf_groups_exist.tex`, tex lines 1034–1336: the section's opening two
sentences, the three sentences of "The self-compression" that are not already
covered elsewhere, the three sentences of the proof of `lem:tau-elementary`,
one sentence each of the proofs of `prop:leavitt-compression` and
`prop:defect`, and the closing sequence of sentences carrying the proof of
`thm:headline` (Theorem B) from `prop:defect` to the final `C^*_r(H)`
contradiction.

Every sentence below is a thin, sentence-scoped repackaging of facts already
proved elsewhere in the tree — `RankTwelveConfiguration`,
`PrintedLeavittEquations`, `SentenceDefectCalculationProofClosure`,
`RankTwelveSimplicity`, `HeadlineTheorem` and `ReducedCStarConsequence` — into
the exact conjunctive shape the printed sentence states.  No new mathematics
is introduced except in two places: `sentence_leavittGroupIntro_defect_eq_top`
and `sentence_defectProof_simple_normally_generates`, which give the
manuscript's *own* printed route from simplicity of `H` to
`𝔇_H(L) = H`, respectively to normal generation by `d`.  The rest of the
tree reaches those same conclusions by an independent, simplicity-free route
(`RankTwelveEndpoint.normalClosure_defect_eq_top`, consumed by
`HeadlineTheorem`'s own proof of `thm:headline`); the two theorems here are
the literal, additional formalizations of the printed *simplicity-based*
argument, not replacements for that route.

## Sentences already carried by an existing declaration

Three of the nineteen sentences assigned to this lane already have an exact
carrier elsewhere in the tree, so no new declaration is added for them here
(a verbatim restatement would be a pure alias and trips the duplicate
detector — see the module docstring of `SentenceCornerCentralizerProofClosure`
and `RankTwelveEJZInstance` for the originals):

* tex key `4be895e9f326` ("So the Steinberg relations give
  `[e_ij(a),e_34(1)]=1`") is exactly
  `RankTwelveEndpoint.manuscriptCornerGenerator_commutator_eq_one`.
* tex key `6134cdd4b823` ("So the theorem of Ershov and Jaikin-Zapirain gives
  property (T) for `EL₁₂(R)` and `EL₃(R)`") is exactly
  `RankTwelveEndpoint.printedBothGroupsHaveKazhdanPropertyT`.
* tex key `6bc686ae28b4` ("Lemma tau-elementary gives `τ∈H`") is exactly
  `RankTwelveEndpoint.printedTauGL_mem`.

The census should be re-keyed to these three names rather than gaining new
wrapper theorems for them.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement
open RankTwelveEndpoint
open ReducedGroupCStarTrace

/-- `H = EL₁₂(L_{𝔽₂}(1,2))` is countable.  Needed to state `IsCDEOperatorMF H`
below; `HeadlineTheorem` and `ReducedCStarConsequence` each declare the same
instance locally, and a `local instance` is not exported to importing
modules. -/
local instance sentenceCountableH : Countable H := RankTwelveEndpoint.countable

/-! ## Section intro (tex lines 1036–1039)

"The Leavitt relations give `τ∈H` with `τLτ⁻¹≤L` for a copy `L` of `EL₃(R)`
and a nontrivial `d∈𝔇_H(L)`.  Simplicity of `H` then gives `𝔇_H(L)=H`."
-/

/-- The printed defect `d = [τcτ⁻¹,ℓ]` lies in the printed intrinsic defect
subgroup `𝔇_H(L)` of the upper-left corner `L = corner`.  This is the
displayed generator membership `printedDefect_generator_mem`, specialized at
the manuscript's own `tau`, `c`, `ell`, and rewritten along the closed
commutator identity `tau_c_commutator_ell`. -/
theorem defect_mem_printedDefect_corner : defect ∈ printedDefect corner := by
  rw [← tau_c_commutator_ell]
  exact printedDefect_generator_mem corner tau_compresses_corner
    c_commutes_corner ell_mem_corner

/-- **Key `2bce533f9741`.**  "The Leavitt relations give `τ∈H` with
`τLτ⁻¹≤L` for a copy `L` of `EL₃(R)` and a nontrivial `d∈𝔇_H(L)`."
(`non_mf_groups_exist.tex`, "The binary Leavitt group", opening sentence.)

The four conjuncts are, in printed order: `τ∈H` (membership of the flattened
matrix in the elementary group, which is what lets `tau` be formed as an
element of `H`); `τLτ⁻¹≤L`; `L` is a copy of `EL₃(R)`, exhibited by the
isomorphism `cornerEquiv`; and the nontrivial defect element `d` lying in the
printed intrinsic defect `𝔇_H(L)`. -/
theorem sentence_leavittGroupIntro_tau_and_defect :
    printedTauGL ∈ elementaryGroup (Fin 12) R ∧
      (∀ gamma ∈ corner, tau * gamma * tau⁻¹ ∈ corner) ∧
      Nonempty (BinaryLeavittSteinberg.ElementaryBase 3 ≃* corner) ∧
      defect ≠ 1 ∧ defect ∈ printedDefect corner :=
  ⟨printedTauGL_mem, tau_compresses_corner, ⟨cornerEquiv⟩, defect_ne_one,
    defect_mem_printedDefect_corner⟩

/-- **Key `d8553fe71e2a`.**  "Simplicity of `H` then gives `𝔇_H(L)=H`."
(`non_mf_groups_exist.tex`, "The binary Leavitt group", second sentence.)

This is the manuscript's own printed route: `𝔇_H(L)` is normal in `H`
(`printedDefect_normal`), so simplicity of `H`
(`RankTwelveEndpoint.manuscriptPropositionSimple`) forces it to be `⊥` or
`⊤`; it cannot be `⊥`, since it contains the nontrivial element `d`
(`defect_mem_printedDefect_corner`, `defect_ne_one`).  This is a genuinely
different derivation from the tree's other, simplicity-free proof of the
same numerical fact `printedDefect_eq_top_of_configuration`
(`RankTwelveEndpoints.lean`), which the rest of the manuscript's own
formalization uses instead; both are recorded because both are printed. -/
theorem sentence_leavittGroupIntro_defect_eq_top : printedDefect corner = ⊤ := by
  haveI : IsSimpleGroup H := manuscriptPropositionSimple
  rcases (printedDefect_normal corner).eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply defect_ne_one
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact defect_mem_printedDefect_corner
  · exact htop

/-! ## "The self-compression" (tex lines 1091–1112) -/

/-- **Key `f634e1e898c5`.**  "Finally, `t₀Ψ(A)s₀=A`, so `Ψ` is injective and
restricts to an injective group homomorphism `GL₃(R)→GL₃(R)`."
(`non_mf_groups_exist.tex`, "The self-compression".)

The three conjuncts are, in printed order: the displayed recovery identity
`t₀Ψ(A)s₀=A`; injectivity of `Ψ = matrixCompression` as a map on matrices;
and injectivity of its restriction `matrixCompressionHom` to the unit group
`GL₃(R)`. -/
theorem sentence_selfCompression_recover_and_injective :
    (∀ M : RankTwelve.Cell R,
        LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0 *
            LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M *
            LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 = M) ∧
      Function.Injective
        (LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily) ∧
      Function.Injective
        (LeavittFamily.matrixCompressionHom (ι := Fin 3) leavittFamily) :=
  ⟨fun M => leavittFamily.matrixCompression_recover M,
    printed_matrixCompression_injective, printed_matrixCompressionHom_injective⟩

/-- **Key `0a5c756b600e`.**  "To realize `Ψ` by conjugation on the embedded
copy of `GL₃(R)`, define the following `6×6` block matrices: `X = …`,
`Y = …`." (`non_mf_groups_exist.tex`, "The self-compression".)

`RankTwelve.shift leavittFamily` and `RankTwelve.shiftInv leavittFamily` are
definitionally the two displayed block matrices `X` and `Y`. -/
theorem sentence_selfCompression_XY_definition :
    RankTwelve.shift leavittFamily =
        !![RankTwelve.kap leavittFamily.s0,
            RankTwelve.kap (leavittFamily.s1 * leavittFamily.t0);
          0, RankTwelve.kap leavittFamily.t1] ∧
      RankTwelve.shiftInv leavittFamily =
        !![RankTwelve.kap leavittFamily.t0, 0;
          RankTwelve.kap (leavittFamily.s0 * leavittFamily.t1),
            RankTwelve.kap leavittFamily.s1] :=
  ⟨rfl, rfl⟩

/-- **Key `b7cf2c6bb850`.**  "A block multiplication using `eq:leavitt` gives
`Y=X⁻¹`." (`non_mf_groups_exist.tex`, "The self-compression".)

Stated as the two-sided inverse identities `XY=YX=I₆`, from which `Y=X⁻¹`
follows. -/
theorem sentence_selfCompression_Y_eq_Xinv :
    RankTwelve.shift leavittFamily * RankTwelve.shiftInv leavittFamily = 1 ∧
      RankTwelve.shiftInv leavittFamily * RankTwelve.shift leavittFamily = 1 :=
  ⟨RankTwelve.shift_mul_shiftInv leavittFamily,
    RankTwelve.shiftInv_mul_shift leavittFamily⟩

/-! ## Proof of `lem:tau-elementary` (tex lines 1147–1163) -/

/-- **Key `82228a3601f0`.**  "For `B∈M_6(R)`, the block matrices
`[I B;0 I]` and `[I 0;B I]` lie in `EL₁₂(R)`: they are the products of the
elementary matrices `e_{r,6+s}(b_rs)`, respectively `e_{6+r,s}(b_rs)`, and no
cross terms arise because distinct off-diagonal matrix units have product
zero." (`non_mf_groups_exist.tex`, proof of `lem:tau-elementary`.)

`B` is `N : RankTwelve.Half R`, the repository's `6×6`-block reading of
`M_6(R)`.  `outerElementary01_val`/`outerElementary10_val` identify the two
displayed block matrices with the elementary-unit values `upperBlock N` and
`lowerBlock N`, and `flat12Units_elementary_mem` is the cited membership,
proved there by exactly the printed decomposition into single-entry
elementary matrices with no cross terms. -/
theorem sentence_tauElementary_blockUnipotents_mem (N : RankTwelve.Half R) :
    ((elementaryUnit (0 : Fin 2) 1 (by decide) N : (RankTwelve.Full R)ˣ) :
        RankTwelve.Full R) = RankTwelve.upperBlock N ∧
      flat12Units (elementaryUnit (0 : Fin 2) 1 (by decide) N) ∈
        elementaryGroup (Fin 12) R ∧
      ((elementaryUnit (1 : Fin 2) 0 (by decide) N : (RankTwelve.Full R)ˣ) :
        RankTwelve.Full R) = RankTwelve.lowerBlock N ∧
      flat12Units (elementaryUnit (1 : Fin 2) 0 (by decide) N) ∈
        elementaryGroup (Fin 12) R :=
  ⟨outerElementary01_val N, flat12Units_elementary_mem 0 1 (by decide) N,
    outerElementary10_val N, flat12Units_elementary_mem 1 0 (by decide) N⟩

/-- **Key `60ac5a649743`.**  Whitehead's identity, displayed.
(`non_mf_groups_exist.tex`, proof of `lem:tau-elementary`.) -/
theorem sentence_tauElementary_whitehead_identity :
    RankTwelve.tau leavittFamily =
      RankTwelve.upperBlock (RankTwelve.shift leavittFamily) *
        RankTwelve.lowerBlock (-RankTwelve.shiftInv leavittFamily) *
        RankTwelve.upperBlock (RankTwelve.shift leavittFamily) *
        RankTwelve.lowerBlock 1 * RankTwelve.upperBlock (-1) *
        RankTwelve.lowerBlock 1 :=
  RankTwelve.tau_eq_whitehead_product leavittFamily

/-- **Key `80a6de61b799`.**  "with `I=I₆` then expresses `τ` as a product of
six matrices of `EL₁₂(R)`." (`non_mf_groups_exist.tex`, proof of
`lem:tau-elementary`.)

The first conjunct is the six-factor product decomposition of `τ` at the
nested level (`tauUnit_eq_six_elementary`); the second identifies the
flattened `printedTauGL` with the flattening of that product
(`printedTauGL_eq_flat12Units`); the third is overall membership
(`printedTauGL_mem`); and the remaining four conjuncts are the individual
membership facts for the (up to repetition) six factors, each an instance of
`flat12Units_elementary_mem`. -/
theorem sentence_tauElementary_tau_product_of_six :
    RankTwelve.tauUnit leavittFamily =
        elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
          elementaryUnit 1 0 (by decide) (-(RankTwelve.shiftInv leavittFamily)) *
          elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
          elementaryUnit 1 0 (by decide) 1 *
          elementaryUnit 0 1 (by decide) (-1) *
          elementaryUnit 1 0 (by decide) 1 ∧
      printedTauGL = flat12Units (RankTwelve.tauUnit leavittFamily) ∧
      printedTauGL ∈ elementaryGroup (Fin 12) R ∧
      flat12Units (elementaryUnit 0 1 (by decide)
          (RankTwelve.shift leavittFamily)) ∈ elementaryGroup (Fin 12) R ∧
      flat12Units (elementaryUnit 1 0 (by decide)
          (-(RankTwelve.shiftInv leavittFamily))) ∈
        elementaryGroup (Fin 12) R ∧
      flat12Units (elementaryUnit 1 0 (by decide) (1 : RankTwelve.Half R)) ∈
        elementaryGroup (Fin 12) R ∧
      flat12Units (elementaryUnit 0 1 (by decide) (-1 : RankTwelve.Half R)) ∈
        elementaryGroup (Fin 12) R :=
  ⟨tauUnit_eq_six_elementary, printedTauGL_eq_flat12Units, printedTauGL_mem,
    flat12Units_elementary_mem 0 1 (by decide) _,
    flat12Units_elementary_mem 1 0 (by decide) _,
    flat12Units_elementary_mem 1 0 (by decide) _,
    flat12Units_elementary_mem 0 1 (by decide) _⟩

/-! ## Proof of `prop:defect` (tex lines 1283–1310) -/

/-- **Key `652fb23b39a2`.**  "The identity `[e_ij(a),e_jk(b)]=e_ik(ab)` then
gives `d=e_02(q)`, which is nontrivial because `q≠0`."
(`non_mf_groups_exist.tex`, proof of `prop:defect`.)

The first conjunct is the printed application of the Steinberg commutator
identity, already proved as `manuscriptMovedMark_Steinberg_commutator`
(`SentenceDefectCalculationProofClosure`); the second and third record the
"nontrivial because `q≠0`" reason. -/
theorem sentence_defectProof_d_nontrivial :
    ⁅elementaryRoot (0 : Fin 12) 1 (by decide) q, ell⁆ = defect ∧
      defect ≠ 1 ∧ q ≠ 0 :=
  ⟨manuscriptMovedMark_Steinberg_commutator, defect_ne_one, q_ne_zero⟩

/-- **Key `d663b0658167`.**  "Since `H` is simple, the nontrivial element `d`
normally generates `H`." (`non_mf_groups_exist.tex`, proof of
`prop:defect`.)

This is the manuscript's own printed route: a normal subgroup of a simple
group is `⊥` or `⊤`, and `normalClosure {defect}` cannot be `⊥` since it
contains the nontrivial element `d = defect`.  As in
`sentence_leavittGroupIntro_defect_eq_top`, this is a different derivation
from the tree's independent, simplicity-free proof of the same numerical
fact, `RankTwelveEndpoint.normalClosure_defect_eq_top`; both are recorded
because the manuscript prints the simplicity-based argument at this point. -/
theorem sentence_defectProof_simple_normally_generates :
    Subgroup.normalClosure ({defect} : Set H) = ⊤ := by
  haveI : IsSimpleGroup H := manuscriptPropositionSimple
  have hmem : defect ∈ Subgroup.normalClosure ({defect} : Set H) :=
    Subgroup.subset_normalClosure rfl
  haveI hnorm : (Subgroup.normalClosure ({defect} : Set H)).Normal :=
    inferInstance
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply defect_ne_one
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact hmem
  · exact htop

/-! ## Proof of `thm:headline` (tex lines 1310–1332) -/

/-- **Key `cfcd74af2c13`.**  "The identities `e_ij(a+b)=e_ij(a)e_ij(b)` and
`[e_ik(a),e_kj(b)]=e_ij(ab)` show inductively that `Y` generates all
elementary matrices over `R`; the commutator identity always has a third
index because `12≥3`." (`non_mf_groups_exist.tex`, proof of
`thm:headline`.)

The three conjuncts are the two displayed identities, each already a
theorem for the elementary/root construction (`elementaryUnit_mul`,
`elementaryRoot_commutator`), and the availability of a third index for
every pair of distinct indices in `Fin 12`
(`Fin.exists_ne_and_ne_of_two_lt`), which is exactly "the commutator
identity always has a third index because `12≥3`". -/
theorem sentence_headlineProof_Y_generation_identities :
    (∀ (i j : Fin 12) (hij : i ≠ j) (a b : R),
        elementaryUnit i j hij a * elementaryUnit i j hij b =
          elementaryUnit i j hij (a + b)) ∧
      (∀ (i j k : Fin 12) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
        ⁅elementaryRoot i j hij a, elementaryRoot j k hjk b⁆ =
          elementaryRoot i k hik (a * b)) ∧
      (∀ i j : Fin 12, i ≠ j → ∃ k : Fin 12, k ≠ i ∧ k ≠ j) :=
  ⟨elementaryUnit_mul, elementaryRoot_commutator,
    fun i j _ => Fin.exists_ne_and_ne_of_two_lt i j (by omega)⟩

/-- **Key `19f03ca278a6`.**  "Thus `H=⟨Y⟩` is finitely generated, and
Proposition `prop:leavitt-compression` of the earlier rank-twelve presentation gives property~(T)."
(`non_mf_groups_exist.tex`, proof of `thm:headline`.) -/
theorem sentence_headlineProof_H_fg_and_propertyT :
    Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H :=
  ⟨RankTwelveEndpoint.finitelyGenerated, RankTwelveEndpoint.hasKazhdanPropertyT⟩

/-- **Key `fc0a614cc21f`.**  "Proposition~\ref{prop:simple} shows that `H` is
nontrivial and simple." (`non_mf_groups_exist.tex`, proof of
`thm:headline`.) -/
theorem sentence_headlineProof_simple_gives_nontrivial_simple :
    Nontrivial H ∧ IsSimpleGroup H :=
  ⟨RankTwelveEndpoint.nontrivial, manuscriptPropositionSimple⟩

/-- **Key `10e55b1f1bc4`.**  "The equality `Rad_MF(H)=H` implies that every
homomorphism from `H` to an MF group is trivial, and so that `H` is not MF."
(`non_mf_groups_exist.tex`, proof of `thm:headline`.)

Both conjuncts are extracted from the already-closed
`HeadlineTheorem.manuscriptBinaryLeavittFullRadical`, whose fourth and fifth
components are the two readings of `Rad_MF(H)=H` that feed exactly this
step. -/
theorem sentence_headlineProof_fullRadical_trivialHoms_notMF :
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1) ∧
      ¬ IsCDEOperatorMF H := by
  obtain ⟨-, -, -, -, -, htriv, hnot⟩ := manuscriptBinaryLeavittFullRadical
  exact ⟨htriv, hnot⟩

/-- **Key `da5ebf3a84e5`.**  "`C^*_r(H)` is separable, and its faithful
canonical trace makes it stably finite." (`non_mf_groups_exist.tex`, proof of
`thm:headline`.) -/
theorem sentence_headlineProof_reducedCStar_separable_stablyFinite :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar H) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar H) := by
  obtain ⟨hsep, hsf, -⟩ := manuscriptReducedCStarConsequence
  exact ⟨hsep, hsf⟩

/-- **Key `327f0dd77bfb`.**  "If an MF embedding `e:C^*_r(H)→𝒬_d` existed
and `p=e(1)`, then `h↦e(λ_h)+(1-p)` would embed `H` in `𝒰(𝒬_d)`, contrary
to the preceding conclusion." (`non_mf_groups_exist.tex`, proof of
`thm:headline`.)

`HasMFEmbedding (ReducedGroupCStar H)` is exactly the existence of such an
`e`; the printed unital correction `h ↦ e(λ_h)+(1-p)` is
`MFAlgebra.nonUnitalStarAlgHomUnitaryMap` composed with the canonical left
regular unitary representation, and the printed contradiction is that this
would make `C^*_r(H)` an MF algebra, contrary to
`manuscriptReducedCStarConsequence`'s third conjunct — while its first
conjunct records that `C^*_r(H)` genuinely is separable, so the failure is
located entirely in the embedding, exactly as printed. -/
theorem sentence_headlineProof_no_MFEmbedding :
    ¬ HasMFEmbedding (ReducedGroupCStar H) := by
  obtain ⟨hsep, -, hnotMF⟩ := manuscriptReducedCStarConsequence
  exact fun hemb => hnotMF ⟨hsep, hemb⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
