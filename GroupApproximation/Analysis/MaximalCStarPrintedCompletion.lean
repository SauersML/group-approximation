import GroupApproximation.Analysis.MaximalCStarAllUniverses

/-!
# The printed `Cmax(H)`: the completion of `ℂ[H]` in the supremum norm

Proof-ledger row `PRE.19`.  The manuscript *defines* the maximal group
C*-algebra as

> the completion of `ℂ[H]` in the supremum of the norms of its unitary
> representations,

and then uses only its universal property.  `Analysis/MaximalGroupCStar` builds
a different object — a closed ⋆-subalgebra of a bounded product of
representations — because that one can be built without a completion argument.
This file builds the printed object and proves the two are ⋆-isomorphic, so the
convenient model is certified as the printed one rather than merely as *a*
model with the same universal property.

## The supremum, and why it is taken over seminorms

Taken literally, "the supremum over the unitary representations" is a supremum
over a proper class, which is why the earlier revision of the proposition
carried a universe clause.  The supremum here is over

  `{p : ℂ[H] → ℝ | p is a C*-seminorm and p(u_h) ≤ 1 for every h}`,

a *set* at the universe of `H`, and `maxGroupSeminorm` is its pointwise
supremum.  This is the same number: every unitary representation contributes
such a seminorm (`isGroupCStarSeminorm_repSeminorm`, using that a unitary of a
C*-algebra has norm at most one), and conversely every such seminorm is the
seminorm of a unitary representation, namely of the canonical representation in
the C*-algebra that `Analysis/CStarSeminormCompletion` builds from it — at the
universe of `H`, so the supremum over the set already ranges over
representations only.  That converse is `repSeminorm_seminormCompletion` below.

The supremum is finite for the reason it always is: `p(Σ c_g g) ≤ Σ |c_g|`
follows from the triangle inequality and `p(c · g) = |c| p(g) ≤ |c|`, an
induction over the finitely many terms of a group-ring element
(`exists_bound_of_isGroupCStarSeminorm`).  That it is again a C*-seminorm is
`CStarSeminormQuotient.isCStarSeminorm_iSup`: squaring is monotone, so the
C*-identity survives a supremum.

## What is proved

* `printedMaximalGroupCStar_existsUnique_lift` — the printed object has the
  printed universal property, for a target in **any** universe.
* `printedMaximalUnitaryHom_injective` — the canonical map `h ↦ u_h` is
  injective.
* `printedMaximalEquiv` — a ⋆-algebra isomorphism onto
  `MaximalGroupCStar H`, the model the rest of the development uses.  Both
  composites are the identity by the uniqueness clauses, which each model has at
  every universe.

## Manuscript status

With `Analysis/MaximalCStarAllUniverses` this is `prop:maximal-cstar` and the
definition it rests on, in the printed form.
-/

namespace GroupApproximation

open scoped CStarAlgebra
open CStarTensor CStarRepresentationNorm

noncomputable section

universe u v

/-! ## Unitaries are contractions -/

/-- A unitary of a C*-algebra has norm at most one.  It has norm exactly one
unless the algebra is trivial, and the trivial case is why the bound is stated
as an inequality: the printed supremum has to be taken over a family that
includes representations on trivial targets. -/
theorem norm_coe_unitary_le_one {B : Type v} [CStarAlgebra B] (u : unitary B) :
    ‖(u : B)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI : Subsingleton B := hB
    rw [Subsingleton.elim (u : B) 0, norm_zero]
    exact zero_le_one
  · letI : Nontrivial B := hB
    exact le_of_eq (CStarRing.norm_of_mem_unitary u.property)

/-! ## The seminorms the supremum is taken over -/

section Seminorms

variable (G : Type u) [Group G]

/-- A C*-seminorm on the group ring under which every group element is a
contraction.  The supremum defining the maximal norm is taken over exactly
these. -/
structure IsGroupCStarSeminorm (p : MonoidAlgebra ℂ G → ℝ) : Prop where
  /-- It is a C*-seminorm. -/
  isCStarSeminorm : IsCStarSeminorm p
  /-- Every group element is a contraction. -/
  single_le_one : ∀ g : G, p (MonoidAlgebra.single g (1 : ℂ)) ≤ 1

/-- The zero seminorm is one, so the family is nonempty.  (It is the seminorm of
the representation on the zero algebra.) -/
theorem isGroupCStarSeminorm_zero : IsGroupCStarSeminorm G (fun _ ↦ 0) where
  isCStarSeminorm :=
    { nonneg := fun _ ↦ le_rfl
      add_le := fun _ _ ↦ le_of_eq (add_zero (0 : ℝ)).symm
      smul := fun c _ ↦ (mul_zero ‖c‖).symm
      mul_le := fun _ _ ↦ le_of_eq (mul_zero (0 : ℝ)).symm
      cstar := fun _ ↦ (mul_zero (0 : ℝ)).symm }
  single_le_one := fun _ ↦ zero_le_one

theorem nonempty_groupCStarSeminorm :
    Nonempty {p : MonoidAlgebra ℂ G → ℝ // IsGroupCStarSeminorm G p} :=
  ⟨⟨fun _ ↦ 0, isGroupCStarSeminorm_zero G⟩⟩

/-- **The family is pointwise bounded**, by the `ℓ¹` norm of the group-ring
element.

The induction is over the linear structure of `ℂ[G]`: the bound for a sum is the
sum of the bounds by the triangle inequality, and for a single term `c · g` it
is `|c|`, because `p(c · g) = |c| p(g)` and `p(g) ≤ 1`.  Stated as "there is a
bound" rather than by naming `Σ|c_g|`, since only boundedness is needed and the
`ℓ¹` norm is not additive. -/
theorem exists_bound_of_isGroupCStarSeminorm (x : MonoidAlgebra ℂ G) :
    ∃ C : ℝ, ∀ p : MonoidAlgebra ℂ G → ℝ, IsGroupCStarSeminorm G p → p x ≤ C := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, fun _ hp ↦ le_of_eq hp.isCStarSeminorm.map_zero⟩
  | add x y hx hy =>
      obtain ⟨C₁, hC₁⟩ := hx
      obtain ⟨C₂, hC₂⟩ := hy
      exact ⟨C₁ + C₂, fun p hp ↦ (hp.isCStarSeminorm.add_le x y).trans
        (add_le_add (hC₁ p hp) (hC₂ p hp))⟩
  | single g c =>
      refine ⟨‖c‖, fun p hp ↦ ?_⟩
      have hsingle : MonoidAlgebra.single g c = c • MonoidAlgebra.single g (1 : ℂ) := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [hsingle, hp.isCStarSeminorm.smul]
      calc ‖c‖ * p (MonoidAlgebra.single g (1 : ℂ))
          ≤ ‖c‖ * 1 :=
            mul_le_mul_of_nonneg_left (hp.single_le_one g) (norm_nonneg c)
        _ = ‖c‖ := mul_one _

theorem bddAbove_groupCStarSeminorm (x : MonoidAlgebra ℂ G) :
    BddAbove (Set.range fun q : {p : MonoidAlgebra ℂ G → ℝ //
      IsGroupCStarSeminorm G p} ↦ q.1 x) := by
  obtain ⟨C, hC⟩ := exists_bound_of_isGroupCStarSeminorm G x
  refine ⟨C, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact hC q.1 q.2

/-- **The maximal C*-seminorm on the group ring**: the supremum of every
C*-seminorm under which the group acts by contractions. -/
def maxGroupSeminorm : MonoidAlgebra ℂ G → ℝ :=
  iSupSeminorm fun q : {p : MonoidAlgebra ℂ G → ℝ // IsGroupCStarSeminorm G p} ↦ q.1

theorem isCStarSeminorm_maxGroupSeminorm : IsCStarSeminorm (maxGroupSeminorm G) :=
  isCStarSeminorm_iSup (nonempty_groupCStarSeminorm G)
    (fun q ↦ q.2.isCStarSeminorm) (bddAbove_groupCStarSeminorm G)

theorem le_maxGroupSeminorm {p : MonoidAlgebra ℂ G → ℝ}
    (hp : IsGroupCStarSeminorm G p) (x : MonoidAlgebra ℂ G) :
    p x ≤ maxGroupSeminorm G x := by
  show p x ≤ ⨆ q : {q : MonoidAlgebra ℂ G → ℝ // IsGroupCStarSeminorm G q}, q.1 x
  exact le_ciSup (bddAbove_groupCStarSeminorm G x) ⟨p, hp⟩

theorem maxGroupSeminorm_single_le_one (g : G) :
    maxGroupSeminorm G (MonoidAlgebra.single g (1 : ℂ)) ≤ 1 := by
  haveI := nonempty_groupCStarSeminorm G
  show (⨆ q : {q : MonoidAlgebra ℂ G → ℝ // IsGroupCStarSeminorm G q},
      q.1 (MonoidAlgebra.single g (1 : ℂ))) ≤ 1
  exact ciSup_le fun q ↦ q.2.single_le_one g

/-- The supremum is itself a member of the family: it is the largest one. -/
theorem isGroupCStarSeminorm_maxGroupSeminorm :
    IsGroupCStarSeminorm G (maxGroupSeminorm G) where
  isCStarSeminorm := isCStarSeminorm_maxGroupSeminorm G
  single_le_one := maxGroupSeminorm_single_le_one G

end Seminorms

/-- **Every unitary representation contributes a member of the family**, so the
supremum over the family dominates the supremum over the representations.  The
universe of the target is unconstrained. -/
theorem isGroupCStarSeminorm_repSeminorm {G : Type u} [Group G] {B : Type v}
    [CStarAlgebra B] (rho : G →* unitary B) :
    IsGroupCStarSeminorm G (repSeminorm rho) where
  isCStarSeminorm := isCStarSeminorm_repSeminorm rho
  single_le_one g := by
    rw [repSeminorm_single]
    exact norm_coe_unitary_le_one (rho g)

/-! ## Agreement of two ⋆-homomorphisms on the group ring -/

/-- Two ⋆-homomorphisms out of the group ring that agree on the group elements
agree everywhere: the group elements span `ℂ[G]` linearly. -/
theorem eq_of_forall_single {G : Type u} [Group G] {C : Type v} [Ring C]
    [StarRing C] [Algebra ℂ C] (f₁ f₂ : MonoidAlgebra ℂ G →⋆ₐ[ℂ] C)
    (h : ∀ g : G, f₁ (MonoidAlgebra.single g (1 : ℂ))
      = f₂ (MonoidAlgebra.single g (1 : ℂ))) (x : MonoidAlgebra ℂ G) :
    f₁ x = f₂ x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single g c =>
      have hsingle : MonoidAlgebra.single g c = c • MonoidAlgebra.single g (1 : ℂ) := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [hsingle, map_smul, map_smul, h g]

/-- **Every C*-seminorm on the group ring is the seminorm of a unitary
representation**, namely of the canonical representation in the C*-algebra it
envelops — which lies at the universe of `G`.

With `isGroupCStarSeminorm_repSeminorm`, which is the other direction, this says
that the supremum over the *set* of group C*-seminorms is the supremum over the
unitary representations, so `maxGroupSeminorm` is the printed norm and not
merely an upper bound for it. -/
theorem repSeminorm_seminormCompletion {G : Type u} [Group G]
    {p : MonoidAlgebra ℂ G → ℝ} (hp : IsCStarSeminorm p) (x : MonoidAlgebra ℂ G) :
    repSeminorm (unitaryHomOfStarAlgHom (toSeminormCompletion hp)) x = p x := by
  have hlift : GroupRingStar.unitaryLift (R := ℂ)
      (unitaryHomOfStarAlgHom (toSeminormCompletion hp)) x
      = toSeminormCompletion hp x := by
    refine eq_of_forall_single _ _ (fun g ↦ ?_) x
    rw [GroupRingStar.unitaryLift_single, one_smul]
    exact unitaryHomOfStarAlgHom_apply (toSeminormCompletion hp) g
  show ‖GroupRingStar.unitaryLift (R := ℂ)
    (unitaryHomOfStarAlgHom (toSeminormCompletion hp)) x‖ = p x
  rw [hlift, norm_toSeminormCompletion]

/-! ## The printed algebra -/

section Printed

variable (G : Type u) [Group G]

/-- **The printed maximal group C*-algebra**: the completion of `ℂ[G]` in the
maximal C*-seminorm. -/
abbrev PrintedMaximalGroupCStar : Type u :=
  SeminormCompletion (isCStarSeminorm_maxGroupSeminorm G)

/-- The canonical unitary representation `h ↦ u_h` of the printed algebra. -/
def printedMaximalUnitaryHom : G →* unitary (PrintedMaximalGroupCStar G) :=
  unitaryHomOfStarAlgHom
    (toSeminormCompletion (isCStarSeminorm_maxGroupSeminorm G))

/-- Two ⋆-homomorphisms out of the printed algebra that agree on the canonical
unitaries are equal, at every universe. -/
theorem printedMaximal_hom_ext {B : Type v} [CStarAlgebra B]
    (f₁ f₂ : PrintedMaximalGroupCStar G →⋆ₐ[ℂ] B)
    (h : ∀ g : G,
      f₁ (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
        = f₂ (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)) :
    f₁ = f₂ := by
  refine seminormCompletion_ext (isCStarSeminorm_maxGroupSeminorm G) f₁ f₂ fun x ↦ ?_
  exact eq_of_forall_single
    (f₁.comp (toSeminormCompletion (isCStarSeminorm_maxGroupSeminorm G)))
    (f₂.comp (toSeminormCompletion (isCStarSeminorm_maxGroupSeminorm G)))
    (fun g ↦ h g) x

/-- **The printed universal property, at every universe.**  For every unital
C*-algebra `B` — in any universe — and every `ρ : G → U(B)` there is a unique
unital ⋆-homomorphism from the completion of `ℂ[G]` in the maximal norm to `B`
carrying `u_g` to `ρ(g)`.

Existence is the fact that the maximal seminorm dominates the representation's
own seminorm, which is exactly what the supremum was taken for. -/
theorem printedMaximalGroupCStar_existsUnique_lift {B : Type v} [CStarAlgebra B]
    (rho : G →* unitary B) :
    ∃! f : PrintedMaximalGroupCStar G →⋆ₐ[ℂ] B,
      ∀ g : G,
        f (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
          = (rho g : B) := by
  have hdom : ∀ x : MonoidAlgebra ℂ G,
      ‖GroupRingStar.unitaryLift (R := ℂ) rho x‖ ≤ maxGroupSeminorm G x :=
    fun x ↦ le_maxGroupSeminorm G (isGroupCStarSeminorm_repSeminorm rho) x
  refine ⟨seminormCompletionLift (isCStarSeminorm_maxGroupSeminorm G)
      (GroupRingStar.unitaryLift (R := ℂ) rho) hdom, ?_, ?_⟩
  · intro g
    have hlift := seminormCompletionLift_apply
      (isCStarSeminorm_maxGroupSeminorm G)
      (GroupRingStar.unitaryLift (R := ℂ) rho) hdom (MonoidAlgebra.single g (1 : ℂ))
    rw [GroupRingStar.unitaryLift_single, one_smul] at hlift
    exact hlift
  · intro q hq
    refine printedMaximal_hom_ext G q _ fun g ↦ ?_
    rw [hq g]
    have hlift := seminormCompletionLift_apply
      (isCStarSeminorm_maxGroupSeminorm G)
      (GroupRingStar.unitaryLift (R := ℂ) rho) hdom (MonoidAlgebra.single g (1 : ℂ))
    rw [GroupRingStar.unitaryLift_single, one_smul] at hlift
    exact hlift.symm

/-! ## The two models agree -/

/-- The comparison map to the product model, from the printed universal property
applied to the product model's own canonical representation.  This is where the
any-universe clause is used: the product model lies one universe above the
printed one. -/
def printedToMaximal :
    PrintedMaximalGroupCStar G →⋆ₐ[ℂ] MaximalGroupCStar G :=
  (printedMaximalGroupCStar_existsUnique_lift G
    (maximalGroupCStarUnitaryHom G)).choose

theorem printedToMaximal_unitary (g : G) :
    printedToMaximal G (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
      = maximalGroupCStarGenerator G g :=
  (printedMaximalGroupCStar_existsUnique_lift G
    (maximalGroupCStarUnitaryHom G)).choose_spec.1 g

/-- The comparison map back, from the product model's own universal property:
the printed algebra lies at the universe of `G`, which is the case the product
model always covered. -/
def maximalToPrinted :
    MaximalGroupCStar G →⋆ₐ[ℂ] PrintedMaximalGroupCStar G :=
  (maximalGroupCStar_existsUnique_lift G (printedMaximalUnitaryHom G)).choose

theorem maximalToPrinted_generator (g : G) :
    maximalToPrinted G (maximalGroupCStarGenerator G g)
      = (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G) :=
  (maximalGroupCStar_existsUnique_lift G (printedMaximalUnitaryHom G)).choose_spec.1 g

theorem maximalToPrinted_comp_printedToMaximal :
    (maximalToPrinted G).comp (printedToMaximal G)
      = StarAlgHom.id ℂ (PrintedMaximalGroupCStar G) := by
  refine printedMaximal_hom_ext G _ _ fun g ↦ ?_
  show maximalToPrinted G (printedToMaximal G
      (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G))
    = (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
  rw [printedToMaximal_unitary, maximalToPrinted_generator]

theorem printedToMaximal_comp_maximalToPrinted :
    (printedToMaximal G).comp (maximalToPrinted G)
      = StarAlgHom.id ℂ (MaximalGroupCStar G) := by
  refine maximalGroupCStar_lift_unique G _ _ fun g ↦ ?_
  show printedToMaximal G (maximalToPrinted G (maximalGroupCStarGenerator G g))
    = maximalGroupCStarGenerator G g
  rw [maximalToPrinted_generator, printedToMaximal_unitary]

/-- **The printed construction and the model the development uses are the same
C*-algebra.**  Both composites are the identity because each model's uniqueness
clause holds at every universe, so it applies to the other model however far
apart the two universes are. -/
def printedMaximalEquiv :
    PrintedMaximalGroupCStar G ≃⋆ₐ[ℂ] MaximalGroupCStar G :=
  StarAlgEquiv.ofStarAlgHom (printedToMaximal G) (maximalToPrinted G)
    (maximalToPrinted_comp_printedToMaximal G)
    (printedToMaximal_comp_maximalToPrinted G)

/-- The comparison carries the printed unitaries to the model's generators, so
the isomorphism is one of *marked* algebras: it respects `h ↦ u_h`. -/
@[simp] theorem printedMaximalEquiv_unitary (g : G) :
    printedMaximalEquiv G (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
      = maximalGroupCStarGenerator G g :=
  printedToMaximal_unitary G g

/-- **The canonical map of the printed algebra is injective**, transported along
the comparison from the same statement for the product model, where it is
witnessed by the concrete left regular representation. -/
theorem printedMaximalUnitaryHom_injective :
    Function.Injective (printedMaximalUnitaryHom G) := by
  intro g h hgh
  apply maximalGroupCStarUnitaryHom_injective G
  apply Subtype.ext
  have hval : (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
      = (printedMaximalUnitaryHom G h : PrintedMaximalGroupCStar G) :=
    congrArg Subtype.val hgh
  have hmap := congrArg (printedToMaximal G) hval
  rw [printedToMaximal_unitary, printedToMaximal_unitary] at hmap
  exact hmap

end Printed

/-- **`p:prelim-cmax`, in the printed form.**  For every group there is a
C*-algebra at the universe of the group — the completion of `ℂ[G]` in the
supremum of the norms of its unitary representations — whose canonical map from
the group is injective, which has the printed universal property for a target in
*any* universe, and which is ⋆-isomorphic to the model
`Analysis/MaximalGroupCStar` builds. -/
theorem manuscriptPrintedMaximalGroupCStar :
    ∀ (G : Type u) [Group G],
      Function.Injective (printedMaximalUnitaryHom G) ∧
      (∀ (B : Type v) [CStarAlgebra B] (rho : G →* unitary B),
        ∃! f : PrintedMaximalGroupCStar G →⋆ₐ[ℂ] B,
          ∀ g : G,
            f (printedMaximalUnitaryHom G g : PrintedMaximalGroupCStar G)
              = (rho g : B)) ∧
      Nonempty (PrintedMaximalGroupCStar G ≃⋆ₐ[ℂ] MaximalGroupCStar G) := by
  intro G _
  exact ⟨printedMaximalUnitaryHom_injective G,
    fun _ _ rho ↦ printedMaximalGroupCStar_existsUnique_lift G rho,
    ⟨printedMaximalEquiv G⟩⟩

end

end GroupApproximation
