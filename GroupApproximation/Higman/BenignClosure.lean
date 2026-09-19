import GroupApproximation.Higman.Benign

/-!
# Closure properties of benign subgroups that direct products supply

Higman's `Lemma 3.6`/`Lemma 3.7` (arXiv:1908.10153 states them as Lemma 3.2
and Lemma 3.3) list the closure properties the whole embedding theorem runs
on:

* `H ∩ H'` and `⟨H, H'⟩` are benign when `H` and `H'` are;
* for `φ : G → N`, the image `φ(H)` is benign when `H` is, and the full
  preimage `φ⁻¹(H)` is benign when `H` is.

Two of the four are direct-product arguments and are proved here in full.
The other two need the normal form theorems for amalgamated products and HNN
extensions --- in the modern presentation they come out of one construction,
Mikaelian's `✻`-construction, as `G ∩ ⟨G^{t₁}, …, G^{tᵣ}⟩ = ⟨A₁, …, Aᵣ⟩` ---
and they are the subject of `Higman.StarConstruction`.

## What is here

* `FPOvergroup` --- the standing hypothesis of the theory: `G` sits inside
  *some* finitely presented group.  Higman's Remark 3.4 is the observation
  that with this hypothesis in force, "benign" does not depend on the ambient
  group, so the notion may be used without naming it.
* `BenignWitness.comap` --- the preimage half of Lemma 3.3, proved.  This is
  the direct product `K_G × K_N` with `G` embedded by `g ↦ (g, φ g)`, and `L`
  taken to be `⊤ × L_N`: an element of `G` lands in it exactly when its image
  lands in `L_N`, which is exactly `φ⁻¹(H)`.  The subgroup `⊤ × L_N` is
  finitely generated because a finitely presented group is finitely
  generated.
* `BenignWitness.infFinset` --- finitely many intersections, by iterating
  `BenignWitness.inf`.

Nothing here is conditional.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.ProductFinitePresentation

variable {G N : Type} [Group G] [Group N]

/-! ## 1.  The standing hypothesis -/

/-- **`G` sits inside a finitely presented group.**  Higman's theory is
stated for finitely generated groups with this property; without it the
notion of benignness in `G` is not stable under change of ambient group
(Higman, Remark 3.4 in the modern write-up). -/
structure FPOvergroup (G : Type) [Group G] where
  /-- The finitely presented overgroup. -/
  K : Type
  /-- Its group structure. -/
  [group : Group K]
  /-- It is finitely presented. -/
  [fp : Group.IsFinitelyPresented K]
  /-- The embedding. -/
  emb : G →* K
  /-- ... which is one. -/
  emb_injective : Function.Injective emb

attribute [instance] FPOvergroup.group FPOvergroup.fp

/-- A finitely presented group is its own overgroup. -/
def FPOvergroup.self (G : Type) [Group G] [Group.IsFinitelyPresented G] :
    FPOvergroup G where
  K := G
  emb := MonoidHom.id G
  emb_injective := fun _ _ h => h

/-- A benign witness is in particular an overgroup. -/
def BenignWitness.toFPOvergroup {H : Subgroup G} (w : BenignWitness H) :
    FPOvergroup G where
  K := w.K
  emb := w.emb
  emb_injective := w.emb_injective

/-- The whole group is benign as soon as it has a finitely presented
overgroup: take `L = ⊤`, which is finitely generated because a finitely
presented group is. -/
def FPOvergroup.benignTop (u : FPOvergroup G) : BenignWitness (⊤ : Subgroup G) where
  K := u.K
  emb := u.emb
  emb_injective := u.emb_injective
  L := ⊤
  L_fg := by
    letI : Group.FG u.K := fg_of_isFinitelyPresented u.K
    exact fg_top
  comap_eq := by
    refine Subgroup.ext fun g => ?_
    constructor
    · intro _
      exact Subgroup.mem_top g
    · intro _
      exact Subgroup.mem_comap.mpr (Subgroup.mem_top _)

/-! ## 2.  Preimages -/

/-- **The preimage half of Lemma 3.3, proved.**

`φ : G →* N` is arbitrary, `H` is benign in `N`, and `G` is assumed only to
have a finitely presented overgroup --- which it must, for the statement to
have content.  The witness is the direct product of the two overgroups with
`G` embedded by `g ↦ (u.emb g, w.emb (φ g))`; the finitely generated subgroup
is `⊤ × L`, finitely generated because `u.K` is finitely presented, hence
finitely generated.

An element `g` of `G` lands in `⊤ × L` exactly when `w.emb (φ g) ∈ L`, i.e.
exactly when `φ g ∈ H`. -/
def BenignWitness.comap (u : FPOvergroup G) (φ : G →* N) {H : Subgroup N}
    (w : BenignWitness H) : BenignWitness (H.comap φ) where
  K := u.K × w.K
  emb := (u.emb).prod (w.emb.comp φ)
  emb_injective := by
    intro x y hxy
    exact u.emb_injective (congrArg Prod.fst hxy)
  L := (⊤ : Subgroup u.K).prod w.L
  L_fg := by
    letI : Group.FG u.K := fg_of_isFinitelyPresented u.K
    exact fg_prod fg_top w.L_fg
  comap_eq := by
    have hw := w.comap_eq
    refine Subgroup.ext fun g => ?_
    constructor
    · intro hg
      have hg' : ((u.emb g, w.emb (φ g)) : u.K × w.K) ∈
          (⊤ : Subgroup u.K).prod w.L := Subgroup.mem_comap.mp hg
      have hg2 : w.emb (φ g) ∈ w.L := (Subgroup.mem_prod.mp hg').2
      have : φ g ∈ H := by
        rw [← hw]
        exact Subgroup.mem_comap.mpr hg2
      exact Subgroup.mem_comap.mpr this
    · intro hg
      have hφ : φ g ∈ H := Subgroup.mem_comap.mp hg
      rw [← hw] at hφ
      refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩)
      exact Subgroup.mem_comap.mp hφ

theorem Benign.comap (u : FPOvergroup G) (φ : G →* N) {H : Subgroup N}
    (h : Benign H) : Benign (H.comap φ) := by
  obtain ⟨w⟩ := h
  exact ⟨w.comap u φ⟩

/-! ## 3.  Iterated intersections -/

/-- Benign subgroups are closed under intersection of a nonempty finite
family, by iterating `BenignWitness.inf`. -/
theorem Benign.iInf_fin {r : ℕ} (A : Fin (r + 1) → Subgroup G)
    (hA : ∀ i, Benign (A i)) : Benign (⨅ i, A i) := by
  induction r with
  | zero =>
      have hsingle : (⨅ i : Fin 1, A i) = A 0 := by
        refine le_antisymm ?_ ?_
        · exact iInf_le _ 0
        · refine le_iInf fun i => ?_
          have : i = 0 := Subsingleton.elim i 0
          rw [this]
      rw [hsingle]
      exact hA 0
  | succ n ih =>
      have hsplit : (⨅ i : Fin (n + 2), A i) =
          A 0 ⊓ ⨅ i : Fin (n + 1), A i.succ := by
        refine le_antisymm ?_ ?_
        · refine le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ)
        · refine le_iInf fun i => ?_
          refine Fin.cases ?_ ?_ i
          · exact inf_le_left
          · intro j
            exact le_trans inf_le_right (iInf_le _ j)
      rw [hsplit]
      exact Benign.inf (hA 0) (ih (fun i => A i.succ) (fun i => hA i.succ))

end Higman
end GroupApproximation
