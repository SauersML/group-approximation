import GroupApproximation.Higman.MikhailovaGraphProductWitness
import GroupApproximation.Higman.RopeTrick

/-!
# `mf_recognition_complexity.tex`: the objects of the two HNN extensions

This file is the Lean form of the displayed definitions of the subsection
"The two HNN extensions", the block between `lem:mikhailova` and
`lem:central-rope`:

```
  K^g = F × P,           L^g = {(f, j q₊(f)) : f ∈ F},
  K_e = K⁰_e × K^g,      L_e = L⁰_e × L^g,      i(f) = (i_e(f), (f,1)),
  Γ_e = ⟨K_e, v | [v, ℓ] = 1 (ℓ ∈ L_e)⟩,        S_e = ⟨i(F), v i(F) v⁻¹⟩.
```

## What is assumed and what is built

The manuscript reaches this point holding two things it has already proved:

* the consequences of `lem:mikhailova` --- a finite alphabet `X_e`, a finite
  relator set `R_e`, marked words `w_x, w_y, w_t` (equivalently the induced
  `f ↦ w_f`), and the equivalence `i_e(f) ∈ L⁰_e ↔ f ∈ N_e`;
* the consequences of `lem:bridge` --- the quotient group `Q₊` with its
  quotient map `q₊`, an injection `j : Q₊ → P`, and `N_e ≤ N₊`.

`RopeInput` bundles exactly those, and nothing else; the fields carrying them
are marked `WIRING` for the lane that supplies them.  Everything after
`RopeInput` is constructed and proved here.

## The stable letter

The manuscript writes the first stable letter as `v` and conjugates by it as
`v i(f) v⁻¹`; the repository's `Higman.Rope` writes the stable letter of
`Higman.CentHNN` as `t` and conjugates as `t⁻¹ (·) t`.  The presentation
`⟨K_e, v | [v, ℓ] = 1 (ℓ ∈ L_e)⟩` is unchanged by replacing the stable letter
by its inverse, so the manuscript's `v` is realized here as `t⁻¹`
(`RopeInput.stableV`), and then `v i(f) v⁻¹` is literally
`Higman.Rope.gammaConj`.

## Reuse

`K_e`, `L_e` and `i` are assembled so that the resulting `BenignWitness` for
`N_e` is the manuscript's; `Γ_e`, `S_e` and `α_e` are then the repository's
`Higman.Rope.Gamma`, `Higman.Rope.Sub` and `Higman.Rope.tau` at that witness.
Nothing is redefined.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Rope

/-! ## 1.  The printed free group `F = F(x,y,t)` and the printed group `P` -/

/-- The printed free group `F = F(x,y,t)`.  Letter `0` is `x`, letter `1` is
`y`, letter `2` is `t`; this is the repository's rank-three compiler source,
so every rank-three lemma applies verbatim. -/
abbrev Fxyt : Type := Higman.MikhailovaRankThree.Source

/-- The printed generator `x`. -/
def genX : Fxyt := FreeGroup.of 0

/-- The printed generator `y`. -/
def genY : Fxyt := FreeGroup.of 1

/-- The printed generator `t`. -/
def genT : Fxyt := FreeGroup.of 2

/-- The printed basis `{x, y, t}` of `F`. -/
def basisXYT : Set Fxyt := Set.range (FreeGroup.of : Fin 3 → Fxyt)

theorem genX_mem_basisXYT : genX ∈ basisXYT := ⟨0, rfl⟩

theorem genY_mem_basisXYT : genY ∈ basisXYT := ⟨1, rfl⟩

theorem genT_mem_basisXYT : genT ∈ basisXYT := ⟨2, rfl⟩

theorem basisXYT_finite : basisXYT.Finite := Set.finite_range _

/-- `x, y, t` generate `F`. -/
theorem closure_basisXYT : Subgroup.closure basisXYT = ⊤ :=
  FreeGroup.closure_range_of (Fin 3)

/-- The printed group `P = F(x₁,y) × F(x₂,t)` of `lem:bridge`(3). -/
abbrev Ptarget : Type := FreeGroup (Fin 2) × FreeGroup (Fin 2)

/-! ## 2.  The input the two preceding lemmas supply -/

/-- **The data the manuscript is holding when it writes `eq:central-rope`.**

The first block is what `lem:mikhailova` produces, the second what
`lem:bridge` produces, and the last two fields are the two printed
consequences that the construction actually consumes:

* `mem_L0_iff` is the closing sentence of `lem:mikhailova`, "the map
  `i_e : F → K⁰_e` is injective and `i_e(f) ∈ L⁰_e` if and only if
  `f ∈ N_e`" --- injectivity is proved here, not assumed, since it is the
  first coordinate;
* `N_le_Nplus` is `lem:bridge`(2), "`N_e ≤ N₊`". -/
structure RopeInput where
  /-- WIRING(higman-compiler): the finite alphabet `X_e` of `lem:mikhailova`. -/
  X : Type
  /-- ... which is finite. -/
  [XFinite : Finite X]
  /-- WIRING(higman-compiler): the finite relator set `R_e`. -/
  R : Set (FreeGroup X)
  /-- ... which is finite. -/
  Rfinite : R.Finite
  /-- WIRING(higman-compiler): `f ↦ w_f`, the map induced by `x ↦ w_x`,
  `y ↦ w_y`, `t ↦ w_t`. -/
  words : Fxyt →* FreeGroup X
  /-- WIRING(bridge-lemma): the printed group `Q₊`. -/
  Qplus : Type
  /-- ... a group. -/
  [QplusGroup : Group Qplus]
  /-- WIRING(bridge-lemma): the printed quotient map `q₊ : F → Q₊`. -/
  qplus : Fxyt →* Qplus
  /-- WIRING(bridge-lemma): the printed injection `j : Q₊ → P` of
  `lem:bridge`(3). -/
  j : Qplus →* Ptarget
  /-- ... which is injective. -/
  j_injective : Function.Injective j
  /-- The printed normal subgroup `N_e ⊴ F`, so that `Q_e = F/N_e`. -/
  N : Subgroup Fxyt
  /-- ... which is normal. -/
  [Nnormal : N.Normal]
  /-- **`lem:mikhailova`, closing sentence.**  `i_e(f) ∈ L⁰_e` if and only if
  `f ∈ N_e`. -/
  mem_L0_iff : ∀ f : Fxyt,
    Higman.MikhailovaRankThree.inputHom words f ∈
        Higman.MikhailovaRankThree.cuttingSubgroup R ↔ f ∈ N
  /-- **`lem:bridge`(2).**  `N_e ≤ N₊`. -/
  N_le_Nplus : N ≤ qplus.ker

attribute [instance] RopeInput.XFinite RopeInput.QplusGroup RopeInput.Nnormal

namespace RopeInput

variable (inp : RopeInput)

/-! ## 3.  `K⁰_e`, `i_e`, `L⁰_e` (`lem:mikhailova`) -/

/-- The printed `K⁰_e = F × F(X_e) × F(X_e)`. -/
abbrev K0 : Type := Higman.MikhailovaRankThree.Ambient inp.X

/-- The printed `i_e(f) = (f, w_f, 1)`. -/
abbrev i0 : Fxyt →* K0 inp :=
  Higman.MikhailovaRankThree.inputHom inp.words

/-- The printed `L⁰_e = F × M_e`. -/
abbrev L0 : Subgroup (K0 inp) :=
  Higman.MikhailovaRankThree.cuttingSubgroup inp.R

/-- The first half of the closing sentence of `lem:mikhailova`: "the first
coordinate makes `i_e` injective". -/
theorem i0_injective : Function.Injective (i0 inp) :=
  Higman.MikhailovaRankThree.inputHom_injective inp.words

/-- `L⁰_e` is finitely generated: it is the whole first free factor times the
finitely generated Mihailova subgroup `M_e`. -/
theorem L0_fg : (L0 inp).FG :=
  Higman.MikhailovaRankThree.cuttingSubgroup_fg inp.Rfinite

/-! ## 4.  `N₊`, `K^g`, `L^g` (`lem:bridge`) -/

/-- The printed `N₊ = ker q₊`. -/
abbrev Nplus : Subgroup Fxyt := inp.qplus.ker

/-- The composite `j ∘ q₊ : F → P` whose graph is `L^g`. -/
abbrev jq : Fxyt →* Ptarget := inp.j.comp inp.qplus

/-- Because `j` is injective, `ker (j q₊) = N₊`: the graph of `j q₊` sees
exactly `N₊`. -/
theorem ker_jq : (jq inp).ker = Nplus inp :=
  Higman.MikhailovaGraphProduct.ker_comp_eq_of_injective inp.qplus inp.j
    inp.j_injective

/-- The printed `K^g = F × P`. -/
abbrev Kg : Type := Fxyt × Ptarget

/-- The printed `L^g = {(f, j q₊(f)) : f ∈ F}`. -/
abbrev Lg : Subgroup Kg :=
  Higman.MikhailovaGraphProduct.graphCutting (jq inp)

theorem mem_Lg_iff (p : Kg) : p ∈ Lg inp ↔ ∃ f : Fxyt, (f, jq inp f) = p := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf⟩

/-- `L^g` is finitely generated: it is the range of a homomorphism out of the
three-generator group `F`. -/
theorem Lg_fg : (Lg inp).FG :=
  Higman.MikhailovaGraphProduct.graphCutting_fg (jq inp)

/-- **The printed generating set of `L^g`.**  "the elements `(a, j q₊(a))` for
`a ∈ {x, y, t}`". -/
theorem Lg_eq_closure :
    Lg inp = Subgroup.closure ((fun a : Fxyt => (a, jq inp a)) '' basisXYT) := by
  have himg : (fun a : Fxyt => (a, jq inp a)) '' basisXYT
      = (Higman.MikhailovaGraphProduct.graphHom (jq inp)) '' basisXYT := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  have hrange : (Higman.MikhailovaGraphProduct.graphHom (jq inp)).range
      = Subgroup.closure
          ((Higman.MikhailovaGraphProduct.graphHom (jq inp)) '' basisXYT) := by
    rw [MonoidHom.range_eq_map, ← closure_basisXYT, MonoidHom.map_closure]
  rw [himg]
  exact hrange

/-! ## 5.  `K_e`, `L_e`, `i` (`eq:central-rope`) -/

/-- The printed `K_e = K⁰_e × K^g`, a direct product of six free groups of
finite rank. -/
abbrev Ke : Type := K0 inp × Kg

/-- The printed `L_e = L⁰_e × L^g`. -/
abbrev Le : Subgroup (Ke inp) := (L0 inp).prod (Lg inp)

/-- The printed `i(f) = (i_e(f), (f, 1))`. -/
abbrev iEmb : Fxyt →* Ke inp := (i0 inp).prod (MonoidHom.inl Fxyt Ptarget)

@[simp] theorem iEmb_apply (f : Fxyt) : iEmb inp f = (i0 inp f, (f, 1)) := rfl

/-- "Injectivity of `i` is clear from the first coordinate." -/
theorem iEmb_injective : Function.Injective (iEmb inp) := by
  intro a b hab
  exact i0_injective inp (congrArg Prod.fst hab)

/-- `L_e` is finitely generated, being the product of the two finitely
generated factors `L⁰_e` and `L^g`. -/
theorem Le_fg : (Le inp).FG := Higman.fg_prod (L0_fg inp) (Lg_fg inp)

/-- The second coordinate of `i(f)` lies in `L^g` exactly when `f ∈ N₊`:
"the second [holds] if and only if `j q₊(f) = 1`, that is, `f ∈ N₊`". -/
theorem pair_mem_Lg_iff (f : Fxyt) : ((f, 1) : Kg) ∈ Lg inp ↔ f ∈ Nplus inp := by
  have h := SetLike.ext_iff.mp
    (Higman.MikhailovaGraphProduct.graphCutting_comap_eq_kernel (jq inp)) f
  rw [Subgroup.mem_comap] at h
  rw [← ker_jq]
  exact h

/-- **`lem:central-rope`(1), the cut, in pullback form.**  "An element `i(f)`
lies in `L_e` if and only if `i_e(f) ∈ L⁰_e` and `(f,1) ∈ L^g`; the first
holds if and only if `f ∈ N_e` by `lem:mikhailova`, and the second if and
only if `j q₊(f) = 1`, that is, `f ∈ N₊`.  Since `N_e ≤ N₊`, the intersection
is `i(N_e)`." -/
theorem comap_Le_eq_N : (Le inp).comap (iEmb inp) = inp.N := by
  ext f
  constructor
  · intro hf
    have h0 : i0 inp f ∈ L0 inp :=
      (Subgroup.mem_prod.mp (Subgroup.mem_comap.mp hf)).1
    exact (inp.mem_L0_iff f).mp h0
  · intro hf
    refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨?_, ?_⟩)
    · exact (inp.mem_L0_iff f).mpr hf
    · exact (pair_mem_Lg_iff inp f).mpr (inp.N_le_Nplus hf)

/-! ## 6.  The benign witness the rope trick consumes -/

/-- **`K_e`, `L_e` and `i`, packaged.**  This is the manuscript's data, not a
new construction: `K` is `K_e`, `emb` is `i`, `L` is `L_e`, and `comap_eq` is
the printed cut in pullback form. -/
def witness : Higman.BenignWitness inp.N where
  K := Ke inp
  emb := iEmb inp
  emb_injective := iEmb_injective inp
  L := Le inp
  L_fg := Le_fg inp
  comap_eq := comap_Le_eq_N inp

@[simp] theorem witness_emb : (witness inp).emb = iEmb inp := rfl

@[simp] theorem witness_L : (witness inp).L = Le inp := rfl

/-! ## 7.  `Γ_e`, `v`, `S_e`, `Q_e`, `α_e` -/

/-- **The printed `Γ_e = ⟨K_e, v | [v, ℓ] = 1 (ℓ ∈ L_e)⟩` of
`eq:central-rope`.**  This is the HNN extension of `K_e` with both edge
groups equal to `L_e` and the identity as edge isomorphism, which is what the
displayed presentation says. -/
abbrev CentralRope : Type := Higman.Rope.Gamma (witness inp)

/-- **The printed stable letter `v`.**  The repository's stable letter is `t`
and conjugates as `t⁻¹ (·) t`, so the manuscript's `v` --- which conjugates
as `v (·) v⁻¹` --- is `t⁻¹`.  The displayed presentation is unchanged by this
substitution, since `[v, ℓ] = 1` if and only if `[v⁻¹, ℓ] = 1`. -/
def stableV : CentralRope inp := (HNNExtension.t)⁻¹

/-- The printed `i(f)`, read inside `Γ_e`. -/
def iGammaHom : Fxyt →* CentralRope inp :=
  (HNNExtension.of).comp (witness inp).emb

@[simp] theorem iGammaHom_eq_gammaOf (f : Fxyt) :
    iGammaHom inp f = Higman.Rope.gammaOf (witness inp) f := rfl

/-- The printed `v i(f) v⁻¹`, read inside `Γ_e`. -/
def vConjHom : Fxyt →* CentralRope inp where
  toFun f := stableV inp * iGammaHom inp f * (stableV inp)⁻¹
  map_one' := by
    show stableV inp * iGammaHom inp 1 * (stableV inp)⁻¹ = 1
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' a b := by
    show stableV inp * iGammaHom inp (a * b) * (stableV inp)⁻¹
      = stableV inp * iGammaHom inp a * (stableV inp)⁻¹ *
        (stableV inp * iGammaHom inp b * (stableV inp)⁻¹)
    rw [map_mul]
    group

@[simp] theorem vConjHom_eq_gammaConj (f : Fxyt) :
    vConjHom inp f = Higman.Rope.gammaConj (witness inp) f := by
  show (HNNExtension.t : CentralRope inp)⁻¹ *
      Higman.Rope.gammaOf (witness inp) f *
      ((HNNExtension.t : CentralRope inp)⁻¹)⁻¹
      = Higman.Rope.gammaConj (witness inp) f
  rw [inv_inv]
  rfl

/-- **The printed `S_e = ⟨i(F), v i(F) v⁻¹⟩` of `eq:central-rope`.** -/
abbrev RopeS : Subgroup (CentralRope inp) := Higman.Rope.Sub (witness inp)

theorem iGammaHom_mem_RopeS (f : Fxyt) : iGammaHom inp f ∈ RopeS inp :=
  Higman.Rope.gammaOf_mem_sub (witness inp) f

theorem vConjHom_mem_RopeS (f : Fxyt) : vConjHom inp f ∈ RopeS inp := by
  rw [vConjHom_eq_gammaConj]
  exact Higman.Rope.gammaConj_mem_sub (witness inp) f

/-- The printed `Q_e = F/N_e`. -/
abbrev Qe : Type := Fxyt ⧸ inp.N

/-- The printed quotient map `q_e : F → Q_e`. -/
abbrev qe : Fxyt →* Qe inp := QuotientGroup.mk' inp.N

/-- **The printed `α_e : S_e → Q_e` of `lem:central-rope`(3).**  Its two
defining values are `alpha_iGamma` and `alpha_vConj` in `CentralRope.lean`. -/
noncomputable def alpha : ↥(RopeS inp) →* Qe inp := Higman.Rope.tau (witness inp)

@[simp] theorem alpha_eq_tau : alpha inp = Higman.Rope.tau (witness inp) := rfl

end RopeInput

end Rope
end MFRecognition
end Manuscript
end GroupApproximation
