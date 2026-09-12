import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.CDEOperatorMF
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.SetTheory.Cardinal.Free

/-!
# Quantitative collapse: perfectness and the commutator decomposition

`non_mf_groups_exist.tex`, `prop:linear-collapse`, steps (i) and (ii).

Step (i).  A finitely generated group whose homomorphisms into countable MF
groups are all trivial is perfect.  The route is the printed one: were `G` not
perfect, its abelianization would be a nontrivial finitely generated abelian
group, which has a nontrivial finite quotient; finite groups are MF
(`isOperatorMF_of_finite_standard`), contradicting the hypothesis.  The
abelian input is the structure theorem
`CommGroup.equiv_free_prod_prod_multiplicative_zmod`: a free coordinate gives a
quotient `ℤ → ℤ/N` on which the chosen element survives, and a torsion
coordinate is already a nontrivial finite quotient.

Step (ii).  In a perfect group with a marked generating tuple every element,
in particular every generator, is the value under `FreeGroup.lift g` of a
product of commutators of *words* in the marks.  The words are obtained by
choosing free-group preimages, which exist because the marking is generating.

Nothing here is analytic: these are statements about groups.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace QuantitativeCollapse

open scoped commutatorElement

/-! ## Consequences of a marking -/

/-- The free-group evaluation at a generating tuple is surjective. -/
theorem lift_surjective {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) :
    Function.Surjective (FreeGroup.lift g) := by
  rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]
  exact hgen

/-- A marked group is finitely generated. -/
theorem fg_of_marked {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) : Group.FG G := by
  classical
  refine ⟨⟨Finset.image g Finset.univ, ?_⟩⟩
  simpa using hgen

/-- A marked group is countable: it is a quotient of the free group on
finitely many letters. -/
theorem countable_of_marked {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) : Countable G :=
  (lift_surjective g hgen).countable

/-! ## A nontrivial finitely generated abelian group has a nontrivial finite quotient -/

/-- If every homomorphism from a finitely generated commutative group into a
finite group is trivial, the group is trivial.

This is the abelian input to step (i).  The proof is the structure theorem:
write the group as `ℤ^j × ∏ ZMod (p i ^ e i)`, take an element `≠ 1`, and read
off a coordinate in which it is nontrivial.  A torsion coordinate is already a
finite quotient; a free coordinate `z ≠ 0` survives in `ZMod (|z| + 1)`. -/
theorem subsingleton_of_finite_targets_trivial (A : Type) [CommGroup A] [Group.FG A]
    (h : ∀ (B : Type) [Group B] [Finite B] (φ : A →* B) (a : A), φ a = 1) :
    Subsingleton A := by
  classical
  by_contra hcon
  have hnt : Nontrivial A := not_subsingleton_iff_nontrivial.mp hcon
  obtain ⟨ι, jj, hι, hjj, p, hp, e, ⟨E⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod A
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have hx : E a ≠ 1 := by
    intro hh
    exact ha (E.injective (by rw [hh, map_one]))
  rcases eq_or_ne (E a).2 1 with h2 | h2
  · -- a free coordinate is nontrivial
    have h1 : (E a).1 ≠ 1 := fun h1 ↦ hx (Prod.ext h1 h2)
    obtain ⟨j0, hj0⟩ : ∃ j0, (E a).1 j0 ≠ 1 := by
      by_contra hcon2
      apply h1
      funext j0
      by_contra hne
      exact hcon2 ⟨j0, hne⟩
    have hzne : Multiplicative.toAdd ((E a).1 j0) ≠ 0 := by
      intro hzz
      exact hj0 (by simpa using congrArg Multiplicative.ofAdd hzz)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (Multiplicative.toAdd ((E a).1 j0)).natAbs + 1 :=
      ⟨_, rfl⟩
    haveI : NeZero N := ⟨by omega⟩
    haveI : Finite (Multiplicative (ZMod N)) :=
      Finite.of_equiv (ZMod N) Multiplicative.ofAdd
    have hne : ((Multiplicative.toAdd ((E a).1 j0) : ℤ) : ZMod N) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdvd
      have hdvd' : N ∣ (Multiplicative.toAdd ((E a).1 j0)).natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hdvd
        simpa using this
      have hpos : 0 < (Multiplicative.toAdd ((E a).1 j0)).natAbs :=
        Int.natAbs_pos.mpr hzne
      have := Nat.le_of_dvd hpos hdvd'
      omega
    have hφ := h (Multiplicative (ZMod N))
      ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod N))).comp
        ((Pi.evalMonoidHom (fun _ : jj ↦ Multiplicative ℤ) j0).comp
          ((MonoidHom.fst (jj → Multiplicative ℤ)
            ((i : ι) → Multiplicative (ZMod (p i ^ e i)))).comp E.toMonoidHom))) a
    have hval : ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod N))).comp
        ((Pi.evalMonoidHom (fun _ : jj ↦ Multiplicative ℤ) j0).comp
          ((MonoidHom.fst (jj → Multiplicative ℤ)
            ((i : ι) → Multiplicative (ZMod (p i ^ e i)))).comp E.toMonoidHom))) a
        = Multiplicative.ofAdd ((Multiplicative.toAdd ((E a).1 j0) : ℤ) : ZMod N) := rfl
    rw [hval] at hφ
    exact hne (by simpa using hφ)
  · -- a torsion coordinate is nontrivial
    obtain ⟨i, hi⟩ : ∃ i, (E a).2 i ≠ 1 := by
      by_contra hcon2
      apply h2
      funext i
      by_contra hne
      exact hcon2 ⟨i, hne⟩
    haveI : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
    haveI : Finite (Multiplicative (ZMod (p i ^ e i))) :=
      Finite.of_equiv (ZMod (p i ^ e i)) Multiplicative.ofAdd
    have hφ := h (Multiplicative (ZMod (p i ^ e i)))
      ((Pi.evalMonoidHom (fun i : ι ↦ Multiplicative (ZMod (p i ^ e i))) i).comp
        ((MonoidHom.snd (jj → Multiplicative ℤ)
          ((i : ι) → Multiplicative (ZMod (p i ^ e i)))).comp E.toMonoidHom)) a
    exact hi hφ

/-! ## Step (i): perfectness -/

/-- **Step (i).**  A finitely generated group all of whose homomorphisms into
countable MF groups are trivial is perfect. -/
theorem commutator_eq_top_of_mfTargets_trivial
    (G : Type) [Group G] [Group.FG G]
    (h : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) :
    commutator G = ⊤ := by
  have hofsurj : Function.Surjective (Abelianization.of : G →* Abelianization G) := by
    rintro ⟨x⟩
    exact ⟨x, rfl⟩
  haveI : Group.FG (Abelianization G) := Group.fg_of_surjective hofsurj
  have hsub : Subsingleton (Abelianization G) := by
    refine subsingleton_of_finite_targets_trivial (Abelianization G) ?_
    intro B _ _ φ b
    obtain ⟨x, rfl⟩ := hofsurj b
    haveI : Countable B := Finite.to_countable
    have hMF : IsCDEOperatorMF B :=
      (isCDEOperatorMF_iff_isOperatorMF B).mpr (isOperatorMF_of_finite_standard B)
    exact h B hMF (φ.comp Abelianization.of) x
  refine eq_top_iff.mpr fun x _ ↦ ?_
  rw [← Abelianization.ker_of G, MonoidHom.mem_ker]
  exact Subsingleton.elim _ _

/-! ## Step (ii): the commutator decomposition of the generators -/

/-- Reversing a list of commutator pairs and swapping each pair inverts the
product of the commutators. -/
theorem prod_commutatorList_swap_reverse {H : Type*} [Group H] (l : List (H × H)) :
    (((l.map Prod.swap).reverse).map fun q ↦ ⁅q.1, q.2⁆).prod
      = ((l.map fun q ↦ ⁅q.1, q.2⁆).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons q l ih =>
      simp only [List.map_cons, List.reverse_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, ih, _root_.mul_inv_rev,
        Prod.fst_swap, Prod.snd_swap]
      rw [← commutatorElement_inv]

/-- **Step (ii).**  In a perfect marked group every element -- in particular
every generator -- is the value of a product of commutators of words in the
marks. -/
theorem exists_commutatorWords {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hperf : commutator G = ⊤) :
    ∃ l : Fin m → List (FreeGroup (Fin m) × FreeGroup (Fin m)),
      ∀ i, FreeGroup.lift g (((l i).map fun q ↦ ⁅q.1, q.2⁆).prod) = g i := by
  classical
  have hsurj : Function.Surjective (FreeGroup.lift g) := lift_surjective g hgen
  have key : ∀ x : G, ∃ l : List (FreeGroup (Fin m) × FreeGroup (Fin m)),
      FreeGroup.lift g ((l.map fun q ↦ ⁅q.1, q.2⁆).prod) = x := by
    intro x
    have hx : x ∈ Subgroup.closure (commutatorSet G) := by
      rw [← commutator_eq_closure, hperf]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨u, v, rfl⟩ := hy
        refine ⟨[(Function.surjInv hsurj u, Function.surjInv hsurj v)], ?_⟩
        simp [map_commutatorElement, Function.surjInv_eq hsurj]
    | one => exact ⟨[], by simp⟩
    | mul y z _ _ ihy ihz =>
        obtain ⟨ly, hly⟩ := ihy
        obtain ⟨lz, hlz⟩ := ihz
        refine ⟨ly ++ lz, ?_⟩
        rw [List.map_append, List.prod_append, map_mul, hly, hlz]
    | inv y _ ihy =>
        obtain ⟨ly, hly⟩ := ihy
        refine ⟨(ly.map Prod.swap).reverse, ?_⟩
        rw [prod_commutatorList_swap_reverse, map_inv, hly]
  choose l hl using fun i ↦ key (g i)
  exact ⟨l, hl⟩

end QuantitativeCollapse
end OneSidedMFRadical
end Manuscript
end GroupApproximation
