import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingPartitions
import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Data.ZMod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Small clopen sets

`simple_kazhdan_sofic_group.tex` at 9047d0d3c, subsection "Simplicity", tex l.189–195 (the proof
is written for `n = 3`, "for `n ≥ 3` replace `3` by `n` throughout", tex l.97–98):

> Let $1\ne K\trianglelefteq G$ and $1\ne g\in K$, and let $w\ge0$ bound the absolute values of
> the exponents in the entries of $g$ and $g^{-1}$. Call a clopen set $V$ small if
> $V\cap T^tV=\varnothing$ for $0<|t|\le2w$ and every $f\circ T^t$, with $|t|\le w$ and $f$ a
> coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$. Minimality and infiniteness imply
> that $T$ has no periodic points, so every nonempty clopen set contains a small one.

* `IsSmallSet T w F V`: the printed "small", for a finite set `F` of coefficient functions;
  `entryCoefficients T n g`: the coefficients of the entries of `g` and `g⁻¹` in `GL_n(R)`;
* `IsSmallSet.mono`: subsets of small sets are small;
* `exists_isSmallSet_nbhd`: every point has a small clopen neighbourhood;
* `exists_isSmallSet_subset`, `exists_isSmallSet_subset_of_minimal`: every nonempty clopen set
  contains a small one (no periodic points by `SimpleKazhdanSofic.zpow_apply_ne_self`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic

open GroupApproximation.ClopenCrossedProduct

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- **Small** (tex l.191–193): `V ∩ T^tV = ∅` for `0 < |t| ≤ 2w`, and every `f ∘ T^t`, `|t| ≤ w`,
`f ∈ F`, is constant on `V`. -/
def IsSmallSet (w : ℕ) (F : Finset (LocallyConstant X (ZMod 2))) (V : Set X) : Prop :=
  (∀ t : ℤ, t ≠ 0 → |t| ≤ ((2 * w : ℕ) : ℤ) → Disjoint V (⇑(T ^ t) '' V)) ∧
    ∀ f ∈ F, ∀ t : ℤ, |t| ≤ (w : ℤ) → ∀ x ∈ V, ∀ y ∈ V, f ((T ^ t) x) = f ((T ^ t) y)

open Classical in
/-- The coefficients of the entries of `g` and `g⁻¹` (tex l.192–193): the Laurent coefficients
`f_t`, `t` in the support, of every entry of `g, g⁻¹ ∈ GL_n(R)`. -/
noncomputable def entryCoefficients (n : ℕ)
    (g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
    Finset (LocallyConstant X (ZMod 2)) :=
  (Finset.univ : Finset (Fin n × Fin n)).biUnion fun pq =>
    (SkewMonoidAlgebra.support ((g : Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))
        pq.1 pq.2)).image (fun t => (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
          ((g : Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) pq.1 pq.2) t)) ∪
    (SkewMonoidAlgebra.support
        (((g⁻¹ : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) pq.1 pq.2)).image
      (fun t => (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff
        (((g⁻¹ : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) pq.1 pq.2) t))

variable {T}

/-- Subsets of small sets are small. -/
theorem IsSmallSet.mono {w : ℕ} {F : Finset (LocallyConstant X (ZMod 2))} {U V : Set X}
    (hVU : V ⊆ U) (hU : IsSmallSet T w F U) : IsSmallSet T w F V :=
  ⟨fun t ht htw => (hU.1 t ht htw).mono hVU (Set.image_mono hVU),
    fun f hf t ht x hx y hy => hU.2 f hf t ht x (hVU hx) y (hVU hy)⟩

variable (T)

/-- **Every point has a small clopen neighbourhood**, for a system without periodic points. -/
theorem exists_isSmallSet_nbhd [TotallySeparatedSpace X]
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y) (w : ℕ)
    (F : Finset (LocallyConstant X (ZMod 2))) (x : X) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ IsSmallSet T w F U := by
  classical
  obtain ⟨U₀, hU₀c, hxU₀, hU₀d⟩ :=
    GroupApproximation.SimpleKazhdanSofic.exists_clopen_nbhd_disjoint_translates T hfree (2 * w) x
  let I : Finset ℤ := Finset.Icc (-(w : ℤ)) w
  refine ⟨U₀ ∩ ⋂ p ∈ F ×ˢ I, ⇑(T ^ p.2) ⁻¹' {y | p.1 y = p.1 ((T ^ p.2) x)},
    hU₀c.inter (isClopen_biInter_finset fun p _ =>
      (p.1.isLocallyConstant.isClopen_fiber _).preimage (T ^ p.2).continuous),
    ⟨hxU₀, Set.mem_iInter₂.mpr fun p _ => rfl⟩,
    fun t ht htw => (hU₀d t ht htw).mono Set.inter_subset_left
      (Set.image_mono Set.inter_subset_left), ?_⟩
  intro f hf t ht y hy z hz
  have hmem : (f, t) ∈ F ×ˢ I := Finset.mem_product.mpr ⟨hf, Finset.mem_Icc.mpr (abs_le.mp ht)⟩
  have h1 : f ((T ^ t) y) = f ((T ^ t) x) := Set.mem_iInter₂.mp hy.2 (f, t) hmem
  have h2 : f ((T ^ t) z) = f ((T ^ t) x) := Set.mem_iInter₂.mp hz.2 (f, t) hmem
  exact h1.trans h2.symm

/-- **Every nonempty clopen set contains a small one** (tex l.194–195), for a system without
periodic points. -/
theorem exists_isSmallSet_subset [TotallySeparatedSpace X]
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y) (w : ℕ)
    (F : Finset (LocallyConstant X (ZMod 2))) {A : Set X} (hA : IsClopen A) (hne : A.Nonempty) :
    ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ V ⊆ A ∧ IsSmallSet T w F V := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hUc, hxU, hU⟩ := exists_isSmallSet_nbhd T hfree w F x
  exact ⟨U ∩ A, hUc.inter hA, ⟨x, hxU, hx⟩, Set.inter_subset_right,
    hU.mono Set.inter_subset_left⟩

/-- **tex l.194–195 as printed**: minimality and infiniteness give no periodic points, so every
nonempty clopen set contains a small one. -/
theorem exists_isSmallSet_subset_of_minimal [T2Space X] [Infinite X] [TotallySeparatedSpace X]
    (hmin : GroupApproximation.SimpleKazhdanSofic.IsMinimalSystem T) (w : ℕ)
    (F : Finset (LocallyConstant X (ZMod 2))) {A : Set X} (hA : IsClopen A) (hne : A.Nonempty) :
    ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ V ⊆ A ∧ IsSmallSet T w F V :=
  exists_isSmallSet_subset T
    (fun _ hj y => GroupApproximation.SimpleKazhdanSofic.zpow_apply_ne_self T hmin hj y) w F hA hne

end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_isSmallSet_nbhd
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_isSmallSet_subset
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_isSmallSet_subset_of_minimal
