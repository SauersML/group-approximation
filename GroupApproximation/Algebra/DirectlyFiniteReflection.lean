import GroupApproximation.Algebra.DirectlyFiniteCorner
import GroupApproximation.Algebra.LEFRingDirectedUnion
import GroupApproximation.Pestov91.LEF
import Mathlib.RingTheory.Ideal.Maps
import GroupApproximation.Meta.AxiomGuard

/-!
# The universal directly finite quotient

`non_mf_groups_exist.tex`, Theorem `thm:core-ring-reflection`
(`\label{thm:core-ring-reflection}`, tex lines 1518–1523):

> Every unital homomorphism from $R_X$ to a directly finite ring factors
> uniquely through restriction $R_X\to R_Y$.  This is also the universal
> stably finite and LEF ring quotient.  The same assertions hold for
> $M_m(R_X)\to M_m(R_Y)$ for every $m\ge1$.  In particular, $R_X$ is
> directly finite if and only if it is stably finite, if and only if it
> is LEF, if and only if every point of $X$ is chain recurrent.

and its proof (tex lines 1527–1530 and 1536–1538):

> A unital homomorphism to a directly finite ring kills every $d$ in
> \eqref{eq:clopen-defect-pair}, hence all of $I$ by
> Lemma~\ref{lem:transient-matrices}.  Since $R_Y$ itself is LEF and
> therefore stably finite, all three universal properties follow.
> [...]  Its quotient
> $M_m(R_Y)$ is LEF, as follows entrywise from finite ring tables.
> Finally, $I=0$ exactly when $X=Y$, giving the stated equivalences.

The deduction uses three facts about restriction `f : R_X →+* R_Y`, so this module
proves it for any surjective unital ring homomorphism `f : R →+* S` such that

1. every unital homomorphism from `R` into a directly finite ring kills `ker f`
   (`KillsKernelOfDirectlyFinite f`, "kills every $d$ ..., hence all of $I$");
2. `S` is LEF ("$R_Y$ itself is LEF");
3. LEF rings are stably finite ("and therefore stably finite").

* `isUniversalQuotients_of_surjective`: the three universal properties.
* `isUniversalQuotients_mapMatrix`: the same for `f.mapMatrix` on `M_m`, through
  `map_eq_zero_of_forall_entry_mem` and `IsLEFRing.matrix` ("entrywise").
* `directlyFinite_iff_stablyFinite_iff_lef_iff_injective`: `R` is directly finite iff
  stably finite iff LEF iff `f` is injective, i.e. `I = 0`.

Fact 3 enters as the named hypothesis Prop `LEFStablyFiniteInterface` (owner chain-core,
S1), discharged by the owner's lemma in the printed assembly.  LEF passes along injections
by `Pestov91.IsLEFRing.of_injective` (`Algebra/LEFRingDirectedUnion.lean`).

The target rings of the universal properties live in an arbitrary universe `w`.
-/

namespace GroupApproximation

open Pestov91

/-! ### The universal properties and the hypothesis Props -/

/-- **`f` is the universal directly finite quotient** (target rings in `Type w`): `S` is
directly finite, and every unital homomorphism from `R` into a directly finite ring
factors uniquely through `f`. -/
def IsUniversalDirectlyFiniteQuotient.{w, u, v} {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) : Prop :=
  IsDedekindFiniteMonoid S ∧
    ∀ (A : Type w) [Ring A] [IsDedekindFiniteMonoid A] (ψ : R →+* A),
      ∃! g : S →+* A, g.comp f = ψ

/-- **`f` is the universal stably finite quotient** (target rings in `Type w`). -/
def IsUniversalStablyFiniteQuotient.{w, u, v} {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) : Prop :=
  IsStablyFiniteRing S ∧
    ∀ (A : Type w) [Ring A] [IsStablyFiniteRing A] (ψ : R →+* A),
      ∃! g : S →+* A, g.comp f = ψ

/-- **`f` is the universal LEF quotient** (target rings in `Type w`). -/
def IsUniversalLEFQuotient.{w, u, v} {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) : Prop :=
  IsLEFRing S ∧
    ∀ (A : Type w) [Ring A], IsLEFRing A → ∀ ψ : R →+* A, ∃! g : S →+* A, g.comp f = ψ

/-- Every unital homomorphism from `R` into a directly finite ring in `Type w` kills the
kernel of `f`.  For restriction `R_X → R_Y` this is the first sentence of the printed
proof. -/
def KillsKernelOfDirectlyFinite.{w, u, v} {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) : Prop :=
  ∀ (A : Type w) [Ring A] [IsDedekindFiniteMonoid A] (ψ : R →+* A) (x : R),
    f x = 0 → ψ x = 0

/-- **Interface, owner chain-core (S1): LEF rings are stably finite** (rings in `Type w`).
The printed "Since $R_Y$ itself is LEF and therefore stably finite" (tex lines
1529–1530). -/
def LEFStablyFiniteInterface.{w} : Prop :=
  ∀ (B : Type w) [Ring B], IsLEFRing B → IsStablyFiniteRing B

/-! ### Model tests of the hypothesis Props -/

/-- Model test: the conclusion of `LEFStablyFiniteInterface` holds on finite rings. -/
theorem lefInterfaces_finite_model (B : Type) [Ring B] [Finite B] :
    IsLEFRing B ∧ IsStablyFiniteRing B :=
  ⟨isLEFRing_of_finite B, inferInstance⟩

/-- Model test: `KillsKernelOfDirectlyFinite` holds for every injective homomorphism. -/
theorem killsKernelOfDirectlyFinite_of_injective.{w, u, v} {R : Type u} {S : Type v} [Ring R]
    [Ring S] (f : R →+* S) (hf : Function.Injective f) : KillsKernelOfDirectlyFinite.{w} f := by
  intro A _ _ ψ x hx
  rw [hf (hx.trans (map_zero f).symm), map_zero]

/-- Model test: the hypotheses of `isUniversalQuotients_of_surjective` and of
`directlyFinite_iff_stablyFinite_iff_lef_iff_injective` are satisfiable, by the identity of a
finite ring. -/
theorem reflection_hypotheses_finite_model (B : Type) [Ring B] [Finite B] :
    Function.Surjective (RingHom.id B) ∧ IsLEFRing B ∧
      KillsKernelOfDirectlyFinite.{0} (RingHom.id B) :=
  ⟨Function.surjective_id, isLEFRing_of_finite B,
    killsKernelOfDirectlyFinite_of_injective _ Function.injective_id⟩

/-- Model test: `KillsKernelOfDirectlyFinite` is not vacuous.  It fails for `ℤ → 0`: the
identity of the directly finite ring `ℤ` does not kill `1`. -/
theorem not_killsKernelOfDirectlyFinite_toZero :
    ¬ KillsKernelOfDirectlyFinite.{0} (Int.castRingHom PUnit.{1}) := by
  intro h
  have h1 : (RingHom.id ℤ) 1 = 0 := h ℤ (RingHom.id ℤ) 1 (Subsingleton.elim _ _)
  simp at h1

/-! ### Factorization through a surjection -/

/-- **Unique factorization.**  A unital homomorphism that kills the kernel of a surjective
`f` factors uniquely through `f`. -/
theorem existsUnique_comp_eq_of_surjective {R S A : Type*} [Ring R] [Ring S] [Ring A]
    (f : R →+* S) (hf : Function.Surjective f) (ψ : R →+* A)
    (hψ : ∀ x, f x = 0 → ψ x = 0) : ∃! g : S →+* A, g.comp f = ψ := by
  have hker : RingHom.ker f ≤ RingHom.ker ψ := fun x hx => by
    simpa using hψ x (by simpa using hx)
  exact ⟨f.liftOfSurjective hf ⟨ψ, hker⟩, RingHom.liftOfSurjective_comp f hf ⟨ψ, hker⟩,
    fun g hg => RingHom.eq_liftOfSurjective f hf ψ hker g hg⟩

/-- Restriction on entries is surjective on matrices. -/
theorem mapMatrix_surjective_of_surjective {R S : Type*} [Ring R] [Ring S] (n : Type*)
    [Fintype n] [DecidableEq n] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (f.mapMatrix : Matrix n n R →+* Matrix n n S) := fun M =>
  ⟨Matrix.of fun i j => Function.surjInv hf (M i j), by
    ext i j
    simp [Function.surjInv_eq hf]⟩

/-- **`φ` kills `M_m(I)`**: the kernel-killing hypothesis passes from `f` to `f.mapMatrix`,
through the corner argument `map_eq_zero_of_forall_entry_mem`. -/
theorem killsKernelOfDirectlyFinite_mapMatrix.{w, u, v} {R : Type u} {S : Type v} [Ring R]
    [Ring S] (f : R →+* S) (hkill : KillsKernelOfDirectlyFinite.{w} f) (m : ℕ) :
    KillsKernelOfDirectlyFinite.{w} (f.mapMatrix : Matrix (Fin m) (Fin m) R →+* _) := by
  intro A _ _ φ M hM
  refine map_eq_zero_of_forall_entry_mem (I := {x | f x = 0}) ?_ φ M ?_
  · intro B _ _ ψ x hx
    exact hkill B ψ x hx
  · intro i j
    simpa using congrArg (fun N => N i j) hM

/-! ### The reflection -/

/-- **The three universal properties.**

`non_mf_groups_exist.tex` (tex lines 1518–1520 and 1527–1530): "Every unital homomorphism
from $R_X$ to a directly finite ring factors uniquely through restriction $R_X\to R_Y$.
This is also the universal stably finite and LEF ring quotient." -/
theorem isUniversalQuotients_of_surjective.{w, u, v} {R : Type u} {S : Type v} [Ring R]
    [Ring S] (hLw : LEFStablyFiniteInterface.{w}) (hLv : LEFStablyFiniteInterface.{v})
    (f : R →+* S) (hf : Function.Surjective f) (hS : IsLEFRing S)
    (hkill : KillsKernelOfDirectlyFinite.{w} f) :
    IsUniversalDirectlyFiniteQuotient.{w} f ∧ IsUniversalStablyFiniteQuotient.{w} f ∧
      IsUniversalLEFQuotient.{w} f := by
  haveI : IsStablyFiniteRing S := hLv S hS
  refine ⟨⟨inferInstance, ?_⟩, ⟨inferInstance, ?_⟩, ⟨hS, ?_⟩⟩
  · intro A _ _ ψ
    exact existsUnique_comp_eq_of_surjective f hf ψ (hkill A ψ)
  · intro A _ _ ψ
    exact existsUnique_comp_eq_of_surjective f hf ψ (hkill A ψ)
  · intro A _ hA ψ
    haveI : IsStablyFiniteRing A := hLw A hA
    exact existsUnique_comp_eq_of_surjective f hf ψ (hkill A ψ)

/-- **Amplification.**

`non_mf_groups_exist.tex` (tex lines 1520–1521 and 1536–1537): "The same assertions hold
for $M_m(R_X)\to M_m(R_Y)$ for every $m\ge1$." and "Its quotient $M_m(R_Y)$ is LEF, as
follows entrywise from finite ring tables." -/
theorem isUniversalQuotients_mapMatrix.{w, u, v} {R : Type u} {S : Type v} [Ring R] [Ring S]
    (hLw : LEFStablyFiniteInterface.{w}) (hLv : LEFStablyFiniteInterface.{v})
    (f : R →+* S) (hf : Function.Surjective f) (hS : IsLEFRing S)
    (hkill : KillsKernelOfDirectlyFinite.{w} f) (m : ℕ) :
    IsUniversalDirectlyFiniteQuotient.{w} (f.mapMatrix : Matrix (Fin m) (Fin m) R →+* _) ∧
      IsUniversalStablyFiniteQuotient.{w} (f.mapMatrix : Matrix (Fin m) (Fin m) R →+* _) ∧
      IsUniversalLEFQuotient.{w} (f.mapMatrix : Matrix (Fin m) (Fin m) R →+* _) :=
  isUniversalQuotients_of_surjective hLw hLv f.mapMatrix
    (mapMatrix_surjective_of_surjective (Fin m) f hf) (hS.matrix (Fin m))
    (killsKernelOfDirectlyFinite_mapMatrix f hkill m)

/-- **The equivalences.**

`non_mf_groups_exist.tex` (tex lines 1521–1523 and 1538): "$R_X$ is directly finite if and
only if it is stably finite, if and only if it is LEF, if and only if every point of $X$
is chain recurrent." and "Finally, $I=0$ exactly when $X=Y$, giving the stated
equivalences."  Here `I = 0` is injectivity of `f`.  A directly finite `R` makes the
identity kill `ker f`; an injective `f` embeds `R` into the LEF ring `S`. -/
theorem directlyFinite_iff_stablyFinite_iff_lef_iff_injective.{u, v} {R : Type u}
    {S : Type v} [Ring R] [Ring S] (hLu : LEFStablyFiniteInterface.{u}) (f : R →+* S)
    (hS : IsLEFRing S) (hkill : KillsKernelOfDirectlyFinite.{u} f) :
    (IsDedekindFiniteMonoid R ↔ IsStablyFiniteRing R) ∧
      (IsStablyFiniteRing R ↔ IsLEFRing R) ∧ (IsLEFRing R ↔ Function.Injective f) := by
  have hinj : IsDedekindFiniteMonoid R → Function.Injective f := fun _ a b hab => by
    have h := hkill R (RingHom.id R) (a - b) (by rw [map_sub, hab, sub_self])
    rw [RingHom.id_apply, sub_eq_zero] at h
    exact h
  have hlef : Function.Injective f → IsLEFRing R := fun hi => IsLEFRing.of_injective hS f hi
  have hsf : IsLEFRing R → IsStablyFiniteRing R := hLu R
  have hdf : IsStablyFiniteRing R → IsDedekindFiniteMonoid R := fun _ => inferInstance
  exact ⟨⟨fun h => hsf (hlef (hinj h)), hdf⟩, ⟨fun h => hlef (hinj (hdf h)), hsf⟩,
    ⟨fun h => hinj (hdf (hsf h)), hlef⟩⟩

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.existsUnique_comp_eq_of_surjective
#audit_axioms GroupApproximation.killsKernelOfDirectlyFinite_mapMatrix
#audit_axioms GroupApproximation.isUniversalQuotients_of_surjective
#audit_axioms GroupApproximation.isUniversalQuotients_mapMatrix
#audit_axioms GroupApproximation.directlyFinite_iff_stablyFinite_iff_lef_iff_injective
#audit_axioms GroupApproximation.reflection_hypotheses_finite_model
#audit_axioms GroupApproximation.not_killsKernelOfDirectlyFinite_toZero
