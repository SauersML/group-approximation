import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Group

/-!
# Infranormal pairs and the escape clause

The Kun--Thom hypothesis on an inclusion `Γ ≤ G` is stated with two words:
`Γ` is **infranormal** in `G` -- its compression semigroup

```text
P_Γ = {g : G | g Γ g⁻¹ ≤ Γ}
```

generates `G` as a group -- and `Γ` is **not normal** in `G`.

This file gives both words a Lean definition and proves the elementary theory
around them.  Nothing here is analytic and nothing here is quoted from a
paper: the compression semigroup is a submonoid because conjugation is a
monoid action, infranormality is a generation statement, and the one
consequence the double construction actually consumes -- the *escape clause* --
is a two-line rearrangement of the negation of normality.

The escape clause matters because it removes four of the six fields of
`Sofic.MFNonsoficDoubleEndpoint.KunThomShulmanDoubleData`.  That interface asks
its caller for a compressor `t`, a marked element `γ ∈ Γ`, and a proof that
`t⁻¹ γ t ∉ Γ`.  Those three data are not an extra hypothesis at all: they exist
for *every* non-normal subgroup, of every group, with no infranormality, no
property (T), and no residual finiteness.  `nonempty_escapeWitness_iff` states
that as an equivalence, so the direction that matters cannot drift out of
sync with the direction that justifies it.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-! ## The compression semigroup -/

/-- The **compression semigroup** of a subgroup: those elements which conjugate
`Γ` into itself.  It is a submonoid rather than a subgroup, and that is the
whole point of the Kun--Thom hypothesis: a one-sided compressor need not have a
one-sided expander for an inverse. -/
def compressionSubmonoid (Γ : Subgroup G) : Submonoid G where
  carrier := {g : G | ∀ γ ∈ Γ, g * γ * g⁻¹ ∈ Γ}
  one_mem' := by
    intro γ hγ
    simpa using hγ
  mul_mem' := by
    intro a b ha hb γ hγ
    have h : a * (b * γ * b⁻¹) * a⁻¹ ∈ Γ := ha _ (hb γ hγ)
    have e : a * b * γ * (a * b)⁻¹ = a * (b * γ * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact h

@[simp] theorem mem_compressionSubmonoid {Γ : Subgroup G} {g : G} :
    g ∈ compressionSubmonoid Γ ↔ ∀ γ ∈ Γ, g * γ * g⁻¹ ∈ Γ := Iff.rfl

/-- The subgroup itself compresses itself. -/
theorem mem_compressionSubmonoid_of_mem (Γ : Subgroup G) :
    ∀ g ∈ Γ, g ∈ compressionSubmonoid Γ := by
  intro g hg γ hγ
  exact Γ.mul_mem (Γ.mul_mem hg hγ) (Γ.inv_mem hg)

/-- Compressors of `Γ` which happen to be invertible as compressors are exactly
the elements of the normalizer. -/
theorem mem_normalizer_of_mem_compressionSubmonoid_of_inv
    {Γ : Subgroup G} {g : G} (hg : g ∈ compressionSubmonoid Γ)
    (hg' : g⁻¹ ∈ compressionSubmonoid Γ) : g ∈ Subgroup.normalizer Γ := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hg h hh
  · intro hh
    have h2 := hg' _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h2

/-! ## Infranormality -/

/-- `Γ` is **infranormal** in `G` when its compressors generate `G`. -/
def IsInfranormal (Γ : Subgroup G) : Prop :=
  Subgroup.closure (compressionSubmonoid Γ : Set G) = ⊤

/-- Every normal subgroup is compressed by every element. -/
theorem compressionSubmonoid_eq_top_of_normal (Γ : Subgroup G) [hΓ : Γ.Normal] :
    compressionSubmonoid Γ = ⊤ := by
  ext g
  simp only [Submonoid.mem_top, iff_true, mem_compressionSubmonoid]
  intro γ hγ
  exact hΓ.conj_mem γ hγ g

/-- Normality is a special case of infranormality; the Kun--Thom hypothesis is
the conjunction of infranormality with the *failure* of this special case. -/
theorem isInfranormal_of_normal (Γ : Subgroup G) [hΓ : Γ.Normal] :
    IsInfranormal Γ := by
  have hmem : ∀ g : G, g ∈ compressionSubmonoid Γ := by
    intro g γ hγ
    exact hΓ.conj_mem γ hγ g
  show Subgroup.closure (compressionSubmonoid Γ : Set G) = ⊤
  rw [Subgroup.eq_top_iff']
  intro g
  exact Subgroup.subset_closure (hmem g)

theorem isInfranormal_top : IsInfranormal (⊤ : Subgroup G) :=
  isInfranormal_of_normal _

theorem isInfranormal_bot : IsInfranormal (⊥ : Subgroup G) :=
  isInfranormal_of_normal _

/-- **A compressor of a finite subgroup is invertible as one.**  Conjugation by
`g` maps `Γ` into `Γ` and is injective, so on a finite `Γ` it is onto, and the
preimage of `γ` is exactly `g⁻¹ γ g`. -/
theorem inv_mem_compressionSubmonoid_of_finite {Γ : Subgroup G} [Finite Γ]
    {g : G} (hg : g ∈ compressionSubmonoid Γ) :
    g⁻¹ ∈ compressionSubmonoid Γ := by
  have hmap : ∀ γ : ↥Γ, g * (γ : G) * g⁻¹ ∈ Γ := fun γ ↦ hg _ γ.2
  set f : ↥Γ → ↥Γ := fun γ ↦ ⟨g * (γ : G) * g⁻¹, hmap γ⟩ with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h2 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro γ hγ
  obtain ⟨δ, hδ⟩ := hsurj ⟨γ, hγ⟩
  have hval : g * (δ : G) * g⁻¹ = γ := congrArg Subtype.val hδ
  have hrw : g⁻¹ * γ * g⁻¹⁻¹ = (δ : G) := by
    rw [← hval]
    group
  rw [hrw]
  exact δ.2

/-- **A finite infranormal subgroup is normal.**  Every compressor of a finite
subgroup lies in the normalizer by
`inv_mem_compressionSubmonoid_of_finite`, so the compressors generate nothing
larger than the normalizer, and infranormality says they generate everything. -/
theorem normal_of_isInfranormal_of_finite {Γ : Subgroup G} [Finite Γ]
    (h : IsInfranormal Γ) : Γ.Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
  rw [← h]
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  exact mem_normalizer_of_mem_compressionSubmonoid_of_inv hg
    (inv_mem_compressionSubmonoid_of_finite hg)

/-- **For a finite subgroup, infranormal and normal are the same condition.**
One direction is `isInfranormal_of_normal`; the other is
`normal_of_isInfranormal_of_finite`.  In particular no finite subgroup is the
peripheral subgroup of a compression pair. -/
theorem isInfranormal_iff_normal_of_finite {Γ : Subgroup G} [Finite Γ] :
    IsInfranormal Γ ↔ Γ.Normal :=
  ⟨normal_of_isInfranormal_of_finite, fun h ↦ isInfranormal_of_normal (hΓ := h) Γ⟩

/-- Infranormality says exactly that every element of the group is a product of
compressors and inverses of compressors. -/
theorem mem_closure_compressionSubmonoid_of_isInfranormal {Γ : Subgroup G}
    (h : IsInfranormal Γ) (g : G) :
    g ∈ Subgroup.closure (compressionSubmonoid Γ : Set G) := by
  rw [h]
  exact Subgroup.mem_top g

/-! ## The escape clause -/

/-- Normality, in the shape the double construction reads it. -/
theorem normal_iff_forall_conj_mem {Γ : Subgroup G} :
    Γ.Normal ↔ ∀ t γ : G, γ ∈ Γ → t⁻¹ * γ * t ∈ Γ := by
  constructor
  · intro h t γ hγ
    simpa using h.conj_mem γ hγ t⁻¹
  · intro h
    refine ⟨fun n hn g ↦ ?_⟩
    have := h g⁻¹ n hn
    simpa using this

/-- **The escape clause.**  A subgroup that is not normal supplies, outright, a
compressor and a marked element whose conjugate escapes.  No infranormality,
no property (T) and no approximation hypothesis enters. -/
theorem exists_escape_of_not_normal {Γ : Subgroup G} (h : ¬ Γ.Normal) :
    ∃ t γ : G, γ ∈ Γ ∧ t⁻¹ * γ * t ∉ Γ := by
  by_contra hcon
  push Not at hcon
  exact h (normal_iff_forall_conj_mem.mpr hcon)

/-- The escape data, bundled.  These are exactly the four combinatorial fields
of `KunThomShulmanDoubleData`. -/
structure EscapeWitness (Γ : Subgroup G) where
  /-- The compressor. -/
  compressor : G
  /-- The marked element of the peripheral subgroup. -/
  marked : G
  /-- The marked element lies in the peripheral subgroup. -/
  marked_mem : marked ∈ Γ
  /-- Conjugating the mark by the compressor leaves the peripheral subgroup. -/
  escapes : compressor⁻¹ * marked * compressor ∉ Γ

/-- An escape witness is exactly an obstruction to normality. -/
theorem EscapeWitness.not_normal {Γ : Subgroup G} (w : EscapeWitness Γ) :
    ¬ Γ.Normal := by
  intro h
  exact w.escapes (normal_iff_forall_conj_mem.mp h _ _ w.marked_mem)

theorem nonempty_escapeWitness_of_not_normal {Γ : Subgroup G}
    (h : ¬ Γ.Normal) : Nonempty (EscapeWitness Γ) := by
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal h
  exact ⟨⟨t, γ, hγ, hesc⟩⟩

/-- The two-way form, so that neither direction can drift. -/
theorem nonempty_escapeWitness_iff {Γ : Subgroup G} :
    Nonempty (EscapeWitness Γ) ↔ ¬ Γ.Normal :=
  ⟨fun ⟨w⟩ ↦ w.not_normal, nonempty_escapeWitness_of_not_normal⟩

/-! ## The Kun--Thom hypothesis on a pair -/

/-- The purely group-theoretic hypothesis of the Kun--Thom theorem on an
inclusion: infranormal, and not normal.  It carries no analytic content, and
it is what the double construction below is run on. -/
structure IsCompressionPair (Γ : Subgroup G) : Prop where
  /-- The compressors of `Γ` generate the ambient group. -/
  infranormal : IsInfranormal Γ
  /-- `Γ` is not normal, so the compression is genuinely one-sided. -/
  not_normal : ¬ Γ.Normal

namespace IsCompressionPair

variable {Γ : Subgroup G}

/-- **The peripheral subgroup of a compression pair is infinite.**  A finite
infranormal subgroup is normal, and a compression pair is not normal. -/
theorem not_finite (h : IsCompressionPair Γ) : ¬ Finite Γ := fun hfin ↦ by
  haveI := hfin
  exact h.not_normal (normal_of_isInfranormal_of_finite h.infranormal)

theorem nonempty_escapeWitness (h : IsCompressionPair Γ) :
    Nonempty (EscapeWitness Γ) :=
  nonempty_escapeWitness_of_not_normal h.not_normal

/-- The compressor of a compression pair, chosen once. -/
noncomputable def escapeWitness (h : IsCompressionPair Γ) : EscapeWitness Γ :=
  h.nonempty_escapeWitness.some

theorem exists_escape (h : IsCompressionPair Γ) :
    ∃ t γ : G, γ ∈ Γ ∧ t⁻¹ * γ * t ∉ Γ :=
  exists_escape_of_not_normal h.not_normal

/-- A compression pair is never the trivial subgroup, and never the whole
group: both of those are normal. -/
theorem ne_bot (h : IsCompressionPair Γ) : Γ ≠ ⊥ := by
  intro hbot
  subst hbot
  exact h.not_normal inferInstance

theorem ne_top (h : IsCompressionPair Γ) : Γ ≠ ⊤ := by
  intro htop
  subst htop
  exact h.not_normal inferInstance

end IsCompressionPair

end GroupApproximation
