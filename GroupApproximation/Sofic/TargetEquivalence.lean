import GroupApproximation.Sofic.LinearResidual
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Sections 53.2--53.4: targets that cannot see the quotient map

Section 53 of the dossier fixes a collection `𝒯` of *approximation targets* --
finite groups, residually finite groups, countable MF groups, finite-dimensional
linear groups over arbitrary fields, compact groups, and unitary groups of norm
matrix coronas -- and calls a homomorphism `q : A → B` a **`𝒯`-equivalence**
when precomposition

`q* : Hom(B, T) → Hom(A, T)`

is a bijection for every `T ∈ 𝒯` (53.7).  The punchline (Theorem 53.3) is that
for the perfect-lamp examples the split projection `q_K : W_K ↠ G_*` is a
`𝒯`-equivalence with nontrivial kernel: the whole target collection is *not
jointly conservative*.

`𝒯` is a collection of groups in every universe, so it is not a Lean object;
but nothing in Section 53 needs it to be one.  Every statement there is the
one-target statement quantified over the members of `𝒯`, and the one-target
statement has a single abstract engine, isolated here:

* `precomp_bijective` -- a surjection whose kernel no `A → T` can see induces a
  bijection on `Hom(−, T)`;
* `precomp_section_rightInverse` -- if the surjection splits, restriction along
  the section is the inverse bijection (Corollary 53.4);
* `not_injective_of_ker_ne_bot` -- and it is still not an isomorphism.

Membership of a particular target class then reduces to a *radical containment*,
which is where the rest of the development enters.  Two such instantiations are
recorded here, one for residually finite targets (via
`finiteResidual_le_ker`) and one for finite-dimensional linear targets over an
arbitrary field (via `linearResidual`); the remaining classes of (53.7) plug in
through exactly the same lemma with their own radical.

The last section records the finite-index half of Theorem 53.5: once the kernel
sits inside `H`, the subgroup `H` is the full preimage of its image and the two
indices agree, so the correspondence of item (1) is available before any of the
target theory.
-/

namespace GroupApproximation

open MatricialStabilityRadical

universe u v w

variable {A : Type u} {B : Type v} {T : Type w} [Group A] [Group B] [Group T]

/-! ## The Hom-set map -/

/-- Precomposition `Hom(B, T) → Hom(A, T)` along `q`, written `q*` in (53.7). -/
def precomp (q : A →* B) (T : Type w) [Group T] : (B →* T) → (A →* T) :=
  fun f => f.comp q

@[simp] theorem precomp_apply (q : A →* B) (f : B →* T) (a : A) :
    precomp q T f a = f (q a) := rfl

/-- `q` is **invisible to the target `T`** when no homomorphism `A → T` sees the
kernel of `q`.  This is the hypothesis that Section 53.2 verifies class by class
by naming a radical of `A` that contains `ker q`. -/
def InvisibleTo (q : A →* B) (T : Type w) [Group T] : Prop :=
  ∀ f : A →* T, q.ker ≤ f.ker

/-! ## The abstract engine of Theorem 53.3 -/

/-- Precomposition along a surjection is injective: a homomorphism out of `B` is
determined by its values on the image of `q`, which is everything. -/
theorem precomp_injective (q : A →* B) (hq : Function.Surjective q) :
    Function.Injective (precomp q T) := by
  intro f₁ f₂ h
  ext b
  obtain ⟨a, rfl⟩ := hq b
  exact DFunLike.congr_fun h a

/-- Precomposition along a surjection invisible to `T` is surjective: a
homomorphism `A → T` killing `ker q` descends along `q`. -/
theorem precomp_surjective (q : A →* B) (hq : Function.Surjective q)
    (hinv : InvisibleTo q T) : Function.Surjective (precomp q T) := by
  intro f
  refine ⟨q.liftOfSurjective hq ⟨f, hinv f⟩, ?_⟩
  ext a
  simp

/-- **Theorem 53.3, abstract form.**  A surjection whose kernel is invisible to
`T` induces a bijection of `Hom`-sets `Hom(B, T) ≃ Hom(A, T)`. -/
theorem precomp_bijective (q : A →* B) (hq : Function.Surjective q)
    (hinv : InvisibleTo q T) : Function.Bijective (precomp q T) :=
  ⟨precomp_injective q hq, precomp_surjective q hq hinv⟩

/-- The `Hom`-set bijection (53.7) as an `Equiv`. -/
noncomputable def precompEquiv (q : A →* B) (hq : Function.Surjective q)
    (hinv : InvisibleTo q T) : (B →* T) ≃ (A →* T) :=
  Equiv.ofBijective _ (precomp_bijective q hq hinv)

/-- ...and it is nevertheless not an isomorphism, as soon as the invisible
kernel is nontrivial.  This is the second half of Theorem 53.3. -/
theorem not_injective_of_ker_ne_bot (q : A →* B) (h : q.ker ≠ ⊥) :
    ¬ Function.Injective q :=
  fun hinj => h (MonoidHom.ker_eq_bot_iff q |>.mpr hinj)

/-! ## Corollary 53.4: the canonical section inverts the bijection -/

section Section534

variable (q : A →* B) (s : B →* A)

/-- Restriction along a section is always a left inverse of precomposition along
the projection, with no hypothesis on the target: this is pure contravariance of
`Hom` applied to `q ∘ s = id`. -/
theorem precomp_section_leftInverse (hs : q.comp s = MonoidHom.id B) :
    Function.LeftInverse (precomp s T) (precomp q T) := by
  intro f
  ext b
  have : q (s b) = b := DFunLike.congr_fun hs b
  simp [precomp, this]

/-- **Corollary 53.4.**  When the projection is a `𝒯`-equivalence, restriction
along the canonical section is a two-sided inverse: every visible representation
of the big group is the unique extension of its restriction to the retract. -/
theorem precomp_section_rightInverse (hq : Function.Surjective q)
    (hinv : InvisibleTo q T) (hs : q.comp s = MonoidHom.id B) :
    Function.RightInverse (precomp s T) (precomp q T) := by
  intro g
  obtain ⟨f, rfl⟩ := precomp_surjective q hq hinv g
  rw [precomp_section_leftInverse q s hs f]

/-- Restriction along the section is itself a bijection `Hom(A, T) ≃ Hom(B, T)`,
inverse to (53.10).  This is (53.11). -/
theorem precomp_section_bijective (hq : Function.Surjective q)
    (hinv : InvisibleTo q T) (hs : q.comp s = MonoidHom.id B) :
    Function.Bijective (precomp s T) :=
  ⟨Function.LeftInverse.injective (precomp_section_rightInverse q s hq hinv hs),
    Function.LeftInverse.surjective (precomp_section_leftInverse (T := T) q s hs)⟩

end Section534

/-! ## Verifying invisibility for two of the target classes -/

section Classes

/-- Finite groups are residually finite: the trivial subgroup already has finite
index, so it belongs to the family the finite residual intersects. -/
theorem isResiduallyFinite_of_finite (T : Type w) [Group T] [Finite T] :
    IsResiduallyFinite T := by
  have hbot : (⊥ : Subgroup T) ∈ {L : Subgroup T | L.FiniteIndex} := by
    refine Set.mem_setOf.mpr ?_
    infer_instance
  refine le_antisymm ?_ bot_le
  exact sInf_le hbot

/-- **Invisibility to residually finite targets.**  If `ker q` lies in the
finite residual then no homomorphism into a residually finite group sees it.
Combined with `precomp_bijective`, this is the residually-finite (hence also the
finite) line of the proof of Theorem 53.3. -/
theorem invisibleTo_of_ker_le_finiteResidual (q : A →* B)
    (h : q.ker ≤ finiteResidual A) (hT : IsResiduallyFinite T) :
    InvisibleTo q T :=
  fun f => h.trans (finiteResidual_le_ker f hT)

/-- The finite-target case of Theorem 53.3. -/
theorem invisibleTo_finite_of_ker_le_finiteResidual (q : A →* B)
    (h : q.ker ≤ finiteResidual A) (T : Type w) [Group T] [Finite T] :
    InvisibleTo q T :=
  invisibleTo_of_ker_le_finiteResidual q h (isResiduallyFinite_of_finite T)

/-- **Invisibility to finite-dimensional linear targets.**  If `ker q` lies in
the all-fields linear residual then no representation `A → GL_d(F)` sees it, for
any field `F` and any dimension `d`.  This is the line of Theorem 53.3 supplied
by Theorem 46.3. -/
theorem invisibleTo_generalLinearGroup_of_ker_le_linearResidual
    {F : Type} [Field F] {d : ℕ} (q : A →* B) (h : q.ker ≤ linearResidual A) :
    InvisibleTo q (Matrix.GeneralLinearGroup (Fin d) F) := by
  intro f x hx
  rw [MonoidHom.mem_ker]
  have hlin : x ∈ linearResidual A := h hx
  have hmat := hlin F ‹Field F› d
    ((Units.coeHom (Matrix (Fin d) (Fin d) F)).comp f)
  refine Units.ext ?_
  simpa using hmat

end Classes

/-! ## Theorem 53.5(1): the finite-index correspondence -/

section FiniteIndex

/-- **Theorem 53.5(1), first half.**  A subgroup containing the kernel is the
full preimage of its image.  In the dossier `H ≥ R_K` comes from Theorem 49.5;
here it is the hypothesis. -/
theorem eq_comap_map_of_ker_le (q : A →* B) {H : Subgroup A} (h : q.ker ≤ H) :
    (H.map q).comap q = H :=
  Subgroup.comap_map_eq_self h

/-- **Theorem 53.5(1), index identity.**  Along a surjection, a subgroup
containing the kernel has the same index as its image; in particular `H` has
finite index in `A` exactly when `q H` has finite index in `B`. -/
theorem index_map_eq_index_of_ker_le (q : A →* B) (hq : Function.Surjective q)
    {H : Subgroup A} (h : q.ker ≤ H) : (H.map q).index = H.index := by
  have h1 := Subgroup.index_comap_of_surjective (H.map q) hq
  rw [eq_comap_map_of_ker_le q h] at h1
  exact h1.symm

/-- **Theorem 53.5(2).**  The restriction `q|_H : H ↠ q H` is surjective, so the
abstract engine above applies verbatim to every node of the finite-index
lattice; its kernel is `ker q` viewed inside `H`. -/
theorem subgroupMap_surjective (q : A →* B) (H : Subgroup A) :
    Function.Surjective (q.subgroupMap H) :=
  MonoidHom.subgroupMap_surjective q H

theorem ker_subgroupMap_eq (q : A →* B) (H : Subgroup A) :
    (q.subgroupMap H).ker = q.ker.subgroupOf H :=
  Subgroup.ext fun _ => Subtype.ext_iff

/-- **Theorem 53.5(3).**  Every node of the finite-index lattice inherits the
`Hom`-set bijection, with no new argument: apply `precomp_bijective` to the
restricted surjection. -/
theorem precomp_subgroupMap_bijective (q : A →* B) (H : Subgroup A)
    (hinv : InvisibleTo (q.subgroupMap H) T) :
    Function.Bijective (precomp (q.subgroupMap H) T) :=
  precomp_bijective _ (subgroupMap_surjective q H) hinv

end FiniteIndex

end GroupApproximation
