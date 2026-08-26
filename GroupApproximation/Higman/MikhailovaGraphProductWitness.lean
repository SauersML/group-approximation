import GroupApproximation.Higman.MikhailovaRankThreeWitness

/-!
# Producting the Mikhailova cut with a graph witness

The finite-presentation compiler uses two independent factors.  The
Mikhailova factor cuts out the recursive kernel.  A graph factor supplies
finite quotient data later, without changing that kernel.  This file proves
the group-theoretic part of that statement with actual benign witnesses.

For a homomorphism `q : F₃ →* P` into a finitely presented group, the range
of `f ↦ (f, q f)` inside `F₃ × P`, intersected with the first factor,
cuts out `ker q`.  Producting this graph witness with the concrete Mikhailova
witness cuts out `N ⊓ ker q`; if `N ≤ ker q`, this is exactly `N`.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaGraphProduct

open GroupApproximation.ProductFinitePresentation
open MikhailovaRankThree

/-- The graph map of a marked quotient representation. -/
def graphHom {P : Type*} [Group P] (q : Source →* P) :
    Source →* Source × P :=
  (MonoidHom.id Source).prod q

@[simp] theorem graphHom_apply {P : Type*} [Group P]
    (q : Source →* P) (f : Source) : graphHom q f = (f, q f) := rfl

/-- The finitely generated graph cutting subgroup. -/
def graphCutting {P : Type*} [Group P] (q : Source →* P) :
    Subgroup (Source × P) :=
  (graphHom q).range

/-- The source is embedded as the first direct-product factor. -/
abbrev graphInput {P : Type*} [Group P] : Source →* Source × P :=
  MonoidHom.inl Source P

theorem graphInput_injective {P : Type*} [Group P] :
    Function.Injective (graphInput (P := P)) := by
  intro f g hfg
  exact congrArg Prod.fst hfg

/-- The graph cut pulls back to the kernel of `q`. -/
theorem graphCutting_comap_eq_kernel {P : Type*} [Group P]
    (q : Source →* P) :
    (graphCutting q).comap graphInput = q.ker := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := Subgroup.mem_comap.mp hf
    obtain ⟨x, hx⟩ := hg
    have hx1 : x = f := congrArg Prod.fst hx
    have hx2 : q x = 1 := congrArg Prod.snd hx
    rw [hx1] at hx2
    exact MonoidHom.mem_ker.mpr hx2
  · intro hf
    have hq : q f = 1 := MonoidHom.mem_ker.mp hf
    apply Subgroup.mem_comap.mpr
    refine ⟨f, ?_⟩
    exact Prod.ext rfl hq

/-- The graph subgroup is finitely generated because the source has rank
three. -/
theorem graphCutting_fg {P : Type*} [Group P] (q : Source →* P) :
    (graphCutting q).FG := by
  letI : Group.FG Source := fg_of_isFinitelyPresented Source
  exact fg_range (graphHom q)

/-- A concrete graph-shaped benign witness for `ker q`. -/
def graphKernelWitness {P : Type*} [Group P]
    [Group.IsFinitelyPresented P] (q : Source →* P) :
    BenignWitness q.ker where
  K := Source × P
  emb := graphInput
  emb_injective := graphInput_injective
  L := graphCutting q
  L_fg := graphCutting_fg q
  comap_eq := graphCutting_comap_eq_kernel q

/-- Injecting the quotient target into a finitely presented graph ambient
does not change the marked kernel. -/
theorem ker_comp_eq_of_injective {Q P : Type*} [Group Q] [Group P]
    (q : Source →* Q) (j : Q →* P) (hj : Function.Injective j) :
    (j.comp q).ker = q.ker := by
  ext f
  constructor
  · intro hf
    apply MonoidHom.mem_ker.mpr
    apply hj
    simpa only [map_one] using MonoidHom.mem_ker.mp hf
  · intro hf
    apply MonoidHom.mem_ker.mpr
    rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hf, map_one]

/-- The graph witness after an explicit embedding in a finitely presented
group.  The intermediate quotient group need not itself be finitely
presented. -/
def embeddedGraphKernelWitness {Q P : Type*} [Group Q] [Group P]
    [Group.IsFinitelyPresented P] (q : Source →* Q) (j : Q →* P)
    (hj : Function.Injective j) : BenignWitness q.ker := by
  let w := graphKernelWitness (j.comp q)
  exact
    { K := w.K
      emb := w.emb
      emb_injective := w.emb_injective
      L := w.L
      L_fg := w.L_fg
      comap_eq := w.comap_eq.trans (ker_comp_eq_of_injective q j hj) }

/-! ## The product checkpoint -/

/-- **Mikhailova plus graph product witness.**  The graph factor leaves the
source normal closure unchanged whenever it kills that closure. -/
def normalClosureProductWitness
    {X P : Type*} [Finite X] [Group P] [Group.IsFinitelyPresented P]
    (S : Set Source) {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    (q : Source →* P) (hSq : Subgroup.normalClosure S ≤ q.ker) :
    BenignWitness (Subgroup.normalClosure S) := by
  let wm := normalClosureWitnessOfMarkedEmbedding S hR words i hi hcomm
  let wg := graphKernelWitness q
  let w := wm.inf wg
  exact
    { K := w.K
      emb := w.emb
      emb_injective := w.emb_injective
      L := w.L
      L_fg := w.L_fg
      comap_eq := w.comap_eq.trans (inf_eq_left.mpr hSq) }

/-- Version where the graph target is first embedded in a finitely presented
ambient group. -/
def normalClosureProductWitnessOfEmbeddedGraph
    {X Q P : Type*} [Finite X] [Group Q] [Group P]
    [Group.IsFinitelyPresented P]
    (S : Set Source) {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    (q : Source →* Q) (j : Q →* P) (hj : Function.Injective j)
    (hSq : Subgroup.normalClosure S ≤ q.ker) :
    BenignWitness (Subgroup.normalClosure S) := by
  let wm := normalClosureWitnessOfMarkedEmbedding S hR words i hi hcomm
  let wg := embeddedGraphKernelWitness q j hj
  let w := wm.inf wg
  exact
    { K := w.K
      emb := w.emb
      emb_injective := w.emb_injective
      L := w.L
      L_fg := w.L_fg
      comap_eq := w.comap_eq.trans (inf_eq_left.mpr hSq) }

end MikhailovaGraphProduct
end Higman
end GroupApproximation
