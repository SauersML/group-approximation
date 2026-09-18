import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Tactic.Abel

/-!
# `Ext¹_ℤ` into a divisible group vanishes

Lane `TWWSchafhauser-3d3`, work order `WO-TWWSchafhauser-3d-3` ("UCT kills the class").
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter, Ann. of Math. 185 (2017), Theorem A, through
C. Schafhauser, J. reine angew. Math. 759 (2020), §4--5.

In Schafhauser's argument the trace-kernel ideal `J` has `K₁(J) = 0` and `K₀(J)` torsion-free
and divisible. The Rosenberg--Schochet sequence (Duke Math. J. 55 (1987), Theorem 1.17)
`0 → Ext¹_ℤ(K_*(S), K_{*+1}(J)) → KK¹(S, J) → Hom(K_*(S), K_*(J)) → 0`
then has zero `Ext` term. This file proves that algebraic input, unconditionally and in
several forms:

* `IsDivisibleGroup`: divisibility by nonzero integers, as a `Prop`;
* `IsDivisibleGroup.baer`: Baer's criterion over `ℤ` (from Mathlib's `Module.Baer.of_divisible`);
* `IsDivisibleGroup.exists_extension`: homomorphisms into a divisible group extend along
  injections, i.e. `Hom(-, D)` sends monomorphisms to epimorphisms;
* `IsDivisibleGroup.exists_retraction`, `IsDivisibleGroup.exists_section`: every extension
  `0 → D → E → Q → 0` of abelian groups with `D` divisible splits. This is `Ext¹_ℤ(Q, D) = 0`
  in its Yoneda form;
* `ext_one_subsingleton_of_isDivisibleGroup`: the same vanishing for Mathlib's derived-category
  `Ext` in `AddCommGrpCat`;
* `gradedExt_one_subsingleton`: the graded `Ext` term
  `Ext¹(K₀ S, K₁ J) × Ext¹(K₁ S, K₀ J)` vanishes when `K₁ J = 0` and `K₀ J` is divisible.
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u v w

noncomputable section

/-- **Divisibility by nonzero integers**, as a proposition: every element has an `n`-th part
for every `n ≠ 0`. This is how the `K₀`-group of Schafhauser's trace-kernel ideal is divisible. -/
def IsDivisibleGroup (D : Type u) [AddCommGroup D] : Prop :=
  ∀ n : ℤ, n ≠ 0 → ∀ a : D, ∃ b : D, n • b = a

namespace IsDivisibleGroup

variable {D : Type u} [AddCommGroup D]

/-- A choice of division witnessing `IsDivisibleGroup`, packaged as Mathlib's `DivisibleBy`. -/
@[implicit_reducible]
def toDivisibleBy (hD : IsDivisibleGroup D) : DivisibleBy D ℤ where
  div a n := if hn : n = 0 then 0 else Classical.choose (hD n hn a)
  div_zero _ := dif_pos (rfl : (0 : ℤ) = 0)
  div_cancel {n} a hn := by
    show n • (if hn : n = 0 then (0 : D) else Classical.choose (hD n hn a)) = a
    rw [dif_neg hn]
    exact Classical.choose_spec (hD n hn a)

/-- Mathlib's `DivisibleBy D ℤ` gives `IsDivisibleGroup D`. -/
theorem of_divisibleBy [DivisibleBy D ℤ] : IsDivisibleGroup D :=
  fun n hn a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel a hn⟩

/-- The zero group is divisible. -/
theorem of_subsingleton [Subsingleton D] : IsDivisibleGroup D :=
  fun _ _ a => ⟨a, Subsingleton.elim _ _⟩

/-- **Baer's criterion over `ℤ`** for a divisible group. -/
theorem baer (hD : IsDivisibleGroup D) : Module.Baer ℤ D := by
  letI : DivisibleBy D ℤ := hD.toDivisibleBy
  exact Module.Baer.of_divisible D

/-- **A divisible group is injective**: a homomorphism into it extends along any injective
homomorphism. -/
theorem exists_extension (hD : IsDivisibleGroup D) {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (hf : Function.Injective f) (g : M →+ D) :
    ∃ h : N →+ D, h.comp f = g :=
  Module.Baer.extension_property_addMonoidHom hD.baer f hf g

/-- **A divisible subgroup is a retract**: every injection out of a divisible group has a
left inverse. -/
theorem exists_retraction (hD : IsDivisibleGroup D) {E : Type v} [AddCommGroup E]
    (i : D →+ E) (hi : Function.Injective i) : ∃ r : E →+ D, ∀ d : D, r (i d) = d := by
  obtain ⟨r, hr⟩ := hD.exists_extension i hi (AddMonoidHom.id D)
  exact ⟨r, fun d => DFunLike.congr_fun hr d⟩

/-- **`Ext¹_ℤ(Q, D) = 0` for divisible `D`, in Yoneda form**: an exact sequence
`0 → D → E → Q → 0` of abelian groups splits, i.e. the quotient map has a homomorphic
section. -/
theorem exists_section (hD : IsDivisibleGroup D) {E : Type v} {Q : Type w}
    [AddCommGroup E] [AddCommGroup Q] (i : D →+ E) (p : E →+ Q)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hcomplex : ∀ d : D, p (i d) = 0) (hexact : ∀ e : E, p e = 0 → ∃ d : D, i d = e) :
    ∃ s : Q →+ E, ∀ q : Q, p (s q) = q := by
  obtain ⟨r, hr⟩ := hD.exists_retraction i hi
  have key : ∀ e e' : E, p e = p e' → e - i (r e) = e' - i (r e') := by
    intro e e' h
    obtain ⟨d, hd⟩ := hexact (e - e') (by rw [map_sub, h, sub_self])
    have h1 : i (r e) - i (r e') = e - e' := by
      rw [← map_sub i, ← map_sub r, ← hd, hr d]
    rw [sub_eq_sub_iff_sub_eq_sub, h1]
  let c : Q → E := fun q => Classical.choose (hp q)
  have hc : ∀ q : Q, p (c q) = q := fun q => Classical.choose_spec (hp q)
  refine ⟨AddMonoidHom.mk' (fun q => c q - i (r (c q))) ?_, ?_⟩
  · intro a b
    show c (a + b) - i (r (c (a + b))) = (c a - i (r (c a))) + (c b - i (r (c b)))
    have hab : p (c (a + b)) = p (c a + c b) := by rw [map_add, hc, hc, hc]
    rw [key (c (a + b)) (c a + c b) hab, map_add r, map_add i]
    abel
  · intro q
    show p (c q - i (r (c q))) = q
    rw [map_sub, hc, hcomplex, sub_zero]

end IsDivisibleGroup

/-! ## The derived-category form -/

/-- **`Ext¹_ℤ(X, D) = 0` for divisible `D`**, for Mathlib's `Ext` groups in the abelian
category `AddCommGrpCat` (for any universe choice `HasExt.{w}`). Divisible groups are
injective objects (`AddCommGrpCat.injective_of_divisible`), and positive `Ext` into an
injective object vanishes. -/
theorem ext_one_subsingleton_of_isDivisibleGroup
    [CategoryTheory.HasExt.{w} AddCommGrpCat.{u}] (X : AddCommGrpCat.{u})
    (D : Type u) [AddCommGroup D] (hD : IsDivisibleGroup D) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w} X (AddCommGrpCat.of D) 1) := by
  letI : DivisibleBy D ℤ := hD.toDivisibleBy
  exact CategoryTheory.Abelian.Ext.subsingleton_of_injective X (AddCommGrpCat.of D) 0

/-- **The `Ext` term of the UCT sequence vanishes for Schafhauser's coefficients.** The
graded `Ext¹_ℤ(K_*(S), K_{*+1}(J))` is `Ext¹(K₀ S, K₁ J) × Ext¹(K₁ S, K₀ J)`. It is zero when
`K₁(J) = 0` and `K₀(J)` is divisible. -/
theorem gradedExt_one_subsingleton [CategoryTheory.HasExt.{w} AddCommGrpCat.{u}]
    (K0S K1S : AddCommGrpCat.{u}) (K0J K1J : Type u) [AddCommGroup K0J] [AddCommGroup K1J]
    [Subsingleton K1J] (h0 : IsDivisibleGroup K0J) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w} K0S (AddCommGrpCat.of K1J) 1 ×
      CategoryTheory.Abelian.Ext.{w} K1S (AddCommGrpCat.of K0J) 1) := by
  haveI : Subsingleton (CategoryTheory.Abelian.Ext.{w} K0S (AddCommGrpCat.of K1J) 1) :=
    ext_one_subsingleton_of_isDivisibleGroup K0S K1J
      (IsDivisibleGroup.of_subsingleton (D := K1J))
  haveI : Subsingleton (CategoryTheory.Abelian.Ext.{w} K1S (AddCommGrpCat.of K0J) 1) :=
    ext_one_subsingleton_of_isDivisibleGroup K1S K0J h0
  refine ⟨fun x y => ?_⟩
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rw [Subsingleton.elim x1 y1, Subsingleton.elim x2 y2]

end

end GroupApproximation.Full.TWWSchafhauser
