import GroupApproximation.GGT.PNaiveTransversal
import Mathlib.GroupTheory.CoprodI

/-!
# Ping-pong between a cyclic subgroup and a partner with a local gap

Third module of property `P_naive` (Abbott--Dahmani, arXiv:1610.04143,
Proposition 2.1 and Theorem 2.2), in the shadow form of this repository.

Let `h` have a local gap at `o` (`GGT/PNaiveShadow.lean`) and put
`ρ = d(o, h·o) − (C+δ)`.  The ping-pong sets are

* `X true`  — the two shadows of `h·o` and `h⁻¹·o` at depth `ρ`;
* `X false` — every translate `g • X true` by a nontrivial `g ∈ ⟨f⟩`.

The one geometric input is **transversality**: every such translate is
transverse to both ends of `h` (Gromov product at most `C + δ` with `h·o` and
with `h⁻¹·o`).  Given it,

* the two sets are disjoint, because a point of `X true` has product at least
  `ρ > C + δ` with one end;
* every nontrivial power of `h` sends `X false` into `X true`, by north--south
  dynamics (`zpow_smul_mem_shadows`);
* every nontrivial `g ∈ ⟨f⟩` sends `X true` into `X false`, by definition;

and Mathlib's ping-pong lemma `Monoid.CoprodI.lift_injective_of_ping_pong`
makes the natural map `⟨f⟩ ∗ ⟨h⟩ → G` injective (`injective_lift_cyclicPair`).
The family is indexed exactly as in `NaiveFreeProduct.cyclicPair`,
`b ↦ cond b ⟨h⟩ ⟨f⟩`, so the conclusion is definitionally
`Function.Injective (NaiveFreeProduct.cyclicPairLift f h)`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through property `P_naive`;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Every nonzero power of a partner with a local gap is nontrivial.** -/
theorem zpow_ne_one_of_local_gap {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h : G} {o : X} (hCδ : 0 ≤ C + δ)
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o)) : ∀ k : ℤ, k ≠ 0 → h ^ k ≠ 1 := by
  have hinf : ¬ IsOfFinOrder h :=
    not_isOfFinOrder_of_isLoxodromic (isLoxodromic_of_local_gap hδ hiso hCδ hloc hgap)
  have hinj : Function.Injective (fun n : ℤ => h ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hinf
  intro k hk hk1
  exact hk (hinj (by simpa using hk1))

/-- **Ping-pong with a transverse cyclic subgroup.**  The natural map from the
free product of `⟨f⟩` and `⟨h⟩` to `G` is injective. -/
theorem injective_lift_cyclicPair {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {f h : G} {o : X} (hf : f ≠ 1) (hCδ : 0 ≤ C + δ)
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o))
    (htrans : ∀ g ∈ Subgroup.zpowers f, g ≠ 1 →
      ∀ x ∈ shadow o (h • o) (dist o (h • o) - (C + δ)) ∪
          shadow o (h⁻¹ • o) (dist o (h • o) - (C + δ)),
        gromovProduct (g • x) (h • o) o ≤ C + δ ∧
          gromovProduct (g • x) (h⁻¹ • o) o ≤ C + δ) :
    Function.Injective
      (Monoid.CoprodI.lift fun b : Bool =>
        (cond b (Subgroup.zpowers h) (Subgroup.zpowers f)).subtype) := by
  classical
  set ρ : ℝ := dist o (h • o) - (C + δ) with hρdef
  have hρ : C + δ < ρ := by
    rw [hρdef]
    linarith
  let Xt : Set X := shadow o (h • o) ρ ∪ shadow o (h⁻¹ • o) ρ
  let Xf : Set X := {x | ∃ g ∈ Subgroup.zpowers f, g ≠ 1 ∧ ∃ x' ∈ Xt, g • x' = x}
  let Xs : Bool → Set X := fun b => cond b Xt Xf
  have hloc' : gromovProduct (h⁻¹ • o) (h • o) o ≤ C := by
    rw [gromovProduct_comm]
    exact hloc
  -- points of `Xf` are transverse to both ends
  have htransf : ∀ x ∈ Xf, gromovProduct x (h • o) o ≤ C + δ ∧
      gromovProduct x (h⁻¹ • o) o ≤ C + δ := by
    rintro x ⟨g, hg, hg1, x', hx', rfl⟩
    exact htrans g hg hg1 x' hx'
  -- the partner has infinite order
  have hne : ∀ k : ℤ, k ≠ 0 → h ^ k ≠ 1 := zpow_ne_one_of_local_gap hδ hiso hCδ hloc hgap
  have hinj : Function.Injective (fun n : ℤ => h ^ n) := by
    intro a b hab
    by_contra hneq
    have hsub : h ^ (a - b) = 1 := by
      simp only at hab
      rw [zpow_sub, hab, mul_inv_cancel]
    exact hne (a - b) (sub_ne_zero.mpr hneq) hsub
  have hinfinite : Infinite (Subgroup.zpowers h) := by
    refine Infinite.of_injective
      (fun n : ℤ => (⟨h ^ n, Subgroup.zpow_mem_zpowers h n⟩ : Subgroup.zpowers h)) ?_
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  have hcard : 3 ≤ Cardinal.mk Bool ∨
      ∃ i : Bool, 3 ≤ Cardinal.mk (cond i (Subgroup.zpowers h) (Subgroup.zpowers f)) := by
    refine Or.inr ⟨true, ?_⟩
    show 3 ≤ Cardinal.mk (Subgroup.zpowers h)
    have h3 : ((3 : ℕ) : Cardinal) < Cardinal.aleph0 := Cardinal.nat_lt_aleph0 3
    have hal : Cardinal.aleph0 ≤ Cardinal.mk (Subgroup.zpowers h) :=
      Cardinal.aleph0_le_mk _
    exact_mod_cast h3.le.trans hal
  have hmemt : h • o ∈ Xt := by
    refine Or.inl ?_
    rw [mem_shadow, gromovProduct_self, dist_comm, hρdef]
    linarith
  have hXne : ∀ b : Bool, (Xs b).Nonempty := by
    rintro (_ | _)
    · exact ⟨f • h • o, f, Subgroup.mem_zpowers f, hf, h • o, hmemt, rfl⟩
    · exact ⟨h • o, hmemt⟩
  have hdisj_tf : Disjoint Xt Xf := by
    refine Set.disjoint_left.mpr ?_
    intro x hxt hxf
    obtain ⟨hpos, hneg⟩ := htransf x hxf
    rcases hxt with hx | hx
    · rw [mem_shadow] at hx
      linarith
    · rw [mem_shadow] at hx
      linarith
  have hXdisj : Pairwise (Disjoint on Xs) := by
    rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · exact hdisj_tf.symm
    · exact hdisj_tf
    · exact absurd rfl hij
  have hpp : Pairwise fun i j => ∀ a : cond i (Subgroup.zpowers h) (Subgroup.zpowers f),
      a ≠ 1 → (cond i (Subgroup.zpowers h) (Subgroup.zpowers f)).subtype a • Xs j ⊆ Xs i := by
    rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · -- a nontrivial element of `⟨f⟩` sends `Xt` into `Xf`
      intro a ha
      rintro _ ⟨x', hx', rfl⟩
      refine ⟨(a : G), a.2, ?_, x', hx', rfl⟩
      intro h1
      exact ha (Subtype.ext h1)
    · -- a nontrivial power of `h` sends `Xf` into `Xt`
      intro a ha
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact ha (Subtype.ext (by simpa using hn.symm))
      obtain ⟨hpos, hneg⟩ := htransf x hx
      show (a : G) • x ∈ Xt
      rw [← hn]
      exact zpow_smul_mem_shadows hδ hiso hloc hgap hpos hneg hn0
    · exact absurd rfl hij
  exact Monoid.CoprodI.lift_injective_of_ping_pong _ hcard Xs hXne hXdisj hpp

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.zpow_ne_one_of_local_gap
#audit_axioms GroupApproximation.GGT.PNaive.injective_lift_cyclicPair
