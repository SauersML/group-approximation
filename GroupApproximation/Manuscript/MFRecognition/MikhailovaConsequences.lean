import GroupApproximation.Manuscript.MFRecognition.EffectiveHigmanCompiler

/-!
# `lem:mikhailova`, the "Consequently" sentence and its proof

The printed lemma continues:

> Consequently, with
> `K^0_e = F × F(X_e) × F(X_e)`, `i_e(f) = (f, w_f, 1)`, `L^0_e = F × M_e`,
> where `w_f` is the image of `f` under `x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t`, the
> map `i_e : F → K^0_e` is injective and `i_e(f) ∈ L^0_e` if and only if
> `f ∈ N_e`.

and its printed proof is:

> The first coordinate makes `i_e` injective, and `(f, w_f, 1) ∈ F × M_e` if
> and only if `w_f = 1` in `Λ_e`, if and only if `q_e(f) = 1` because the
> embedding is injective, if and only if `f ∈ N_e`.

Every sentence here is proved.  The three objects are the repository's
`Higman.MikhailovaRankThree` objects at the marked words of the compiler
output, and the three links of the printed chain are, in order,
`MikhailovaRankThree.input_mem_cutting_iff`,
`MarkedHigmanOutput.hostQuotient_markedWord_eq_one_iff_quotientQ` (which is
`MikhailovaRankThree.kernel_eq_normalClosure_of_markedEmbedding`, the printed
"because the embedding is injective"), and `quotientQ_eq_one_iff`.

Nothing in this module depends on `EffectiveHigmanCompiler`: it consumes a
`MarkedHigmanOutput`, however obtained.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler

open Higman

noncomputable section

namespace MarkedHigmanOutput

variable {P : RecPresCode} (o : MarkedHigmanOutput P)

/-! ## 1.  The three printed objects -/

/-- The printed `K^0_e = F × F(X_e) × F(X_e)`. -/
abbrev K0 : Type := MikhailovaRankThree.Ambient (HostAlphabet o.host)

/-- The printed `i_e(f) = (f, w_f, 1)`. -/
def iHom : Source →* o.K0 :=
  MikhailovaRankThree.inputHom o.markedWord

/-- The printed formula `i_e(f) = (f, w_f, 1)`. -/
theorem iHom_apply (f : Source) : o.iHom f = (f, o.markedWord f, 1) :=
  MikhailovaRankThree.inputHom_apply o.markedWord f

/-- The printed `L^0_e = F × M_e`: the whole first factor times the Mihailova
subgroup. -/
def L0 : Subgroup o.K0 :=
  MikhailovaRankThree.cuttingSubgroup (hostRelators o.host)

/-- `L^0_e = F × M_e`, read elementwise: membership constrains only the
`F(X_e) × F(X_e)` coordinate, and there it is membership in `M_e`. -/
theorem mem_L0_iff (p : o.K0) : p ∈ o.L0 ↔ p.2 ∈ o.mihailova := by
  show p ∈ (⊤ : Subgroup Source).prod
    (Mikhailova.freeSubgroup (hostRelators o.host)) ↔ _
  constructor
  · intro hp
    exact (Subgroup.mem_prod.mp hp).2
  · intro hp
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hp⟩

/-! ## 2.  The two printed consequences -/

/-- **The printed "the map `i_e : F → K^0_e` is injective".**  Its proof is the
printed "the first coordinate makes `i_e` injective". -/
theorem iHom_injective : Function.Injective o.iHom :=
  MikhailovaRankThree.inputHom_injective o.markedWord

/-- First link of the printed chain: `(f, w_f, 1) ∈ F × M_e` if and only if
`w_f = 1` in `Λ_e`. -/
theorem iHom_mem_L0_iff_markedWord_eq_one (f : Source) :
    o.iHom f ∈ o.L0 ↔ hostQuotient o.host (o.markedWord f) = 1 :=
  MikhailovaRankThree.input_mem_cutting_iff (hostRelators o.host)
    o.markedWord f

/-- Second link of the printed chain: `w_f = 1` in `Λ_e` if and only if
`q_e(f) = 1`, "because the embedding is injective". -/
theorem iHom_mem_L0_iff_quotientQ_eq_one (f : Source) :
    o.iHom f ∈ o.L0 ↔ quotientQ P f = 1 :=
  (o.iHom_mem_L0_iff_markedWord_eq_one f).trans
    (o.hostQuotient_markedWord_eq_one_iff_quotientQ f)

/-- **The printed "`i_e(f) ∈ L^0_e` if and only if `f ∈ N_e`".**  Third link of
the printed chain: `q_e(f) = 1` if and only if `f ∈ N_e`. -/
theorem iHom_mem_L0_iff_mem_kernelN (f : Source) :
    o.iHom f ∈ o.L0 ↔ f ∈ kernelN P :=
  (o.iHom_mem_L0_iff_quotientQ_eq_one f).trans (quotientQ_eq_one_iff P f)

/-! ## 3.  Subgroup forms, for the two HNN extensions -/

/-- The same consequence as an equation of subgroups of `F`: `L^0_e` pulls
back along `i_e` to `N_e`.  This is the form `lem:central-rope` consumes as
`i(F) ∩ L_e = i(N_e)`. -/
theorem comap_L0_eq_kernelN : o.L0.comap o.iHom = kernelN P :=
  (MikhailovaRankThree.comap_cutting_eq_kernel (hostRelators o.host)
    o.markedWord).trans o.markedWord_ker

/-- The intersection form inside the ambient: `i_e(F) ∩ L^0_e = i_e(N_e)`. -/
theorem range_inf_L0_eq_map_kernelN :
    o.iHom.range ⊓ o.L0 = (kernelN P).map o.iHom :=
  MikhailovaRankThree.range_inf_cutting_eq_normalClosure_map
    (rank3Relators P) (hostRelators o.host) o.markedWord o.emb o.emb_injective
    o.emb_comm

/-- `L^0_e` is finitely generated: `F` is free of finite rank and `M_e` has the
displayed finite generating set. -/
theorem L0_fg : o.L0.FG :=
  MikhailovaRankThree.cuttingSubgroup_fg (hostRelators_finite o.host)

/-- The compiler output, packaged as the repository's benign witness for
`N_e`: the finitely presented ambient `K^0_e`, the injection `i_e`, and the
finitely generated `L^0_e` cutting out exactly `N_e`.  This is the object
`lem:central-rope` and `thm:hnn-permanence` consume. -/
def benignWitness : BenignWitness (kernelN P) :=
  MikhailovaRankThree.normalClosureWitnessOfMarkedEmbedding
    (rank3Relators P) (hostRelators_finite o.host) o.markedWord o.emb
    o.emb_injective o.emb_comm

include o in
/-- `N_e` is benign, in the repository's sense.  The witness is `o`, which
appears only in the proof, so it is `include`d explicitly. -/
theorem benign_kernelN : Benign (kernelN P) :=
  Benign.mk' o.benignWitness

/-! ## 4.  Wiring note for the rope lane

`Manuscript/MFRecognition/RopeObjects.lean` declares `Rope.RopeInput` with
seven fields marked `WIRING(higman-compiler)`.  This lane does not import that
module (it is not on `origin/main` yet), so the adapter is recorded here and
the coordinator can add it in one declaration.  Field by field, from
`o : MarkedHigmanOutput P`:

* `X := HigmanCompiler.HostAlphabet o.host` (a `Fin` type, so `XFinite` is
  `inferInstance`);
* `R := HigmanCompiler.hostRelators o.host` and
  `Rfinite := HigmanCompiler.hostRelators_finite o.host`;
* `words := o.markedWord`;
* `N := HigmanCompiler.kernelN P`, whose `Nnormal` is
  `Subgroup.normalClosure_normal`;
* `mem_L0_iff := o.iHom_mem_L0_iff_mem_kernelN`, whose statement is
  definitionally the field's type, since `o.iHom` is
  `MikhailovaRankThree.inputHom o.markedWord` and `o.L0` is
  `MikhailovaRankThree.cuttingSubgroup (hostRelators o.host)`.

The remaining `RopeInput` fields (`Qplus`, `qplus`, `j`, `j_injective`,
`N_le_Nplus`) belong to `lem:bridge`, not to `lem:mikhailova`.
-/

end MarkedHigmanOutput

end

end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
