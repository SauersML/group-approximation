import GroupApproximation.Sofic.FiniteDimensionalResidual

/-!
# Section 41: when the three approximation radicals coincide

Three radicals are attached to a group: the MF radical (invisible to every
matrix-corona representation), the finite-dimensional unitary residual
(invisible to every finite-dimensional unitary representation), and the finite
residual (invisible to every finite quotient).  In general they only sit in a
chain, `Res_MF ≤ Rad_fd ≤ Res_fin`, proved in
`Sofic.FiniteDimensionalResidual`.

This file supplies the mechanism that collapses the chain, in the abstract form
the dossier's concrete family instantiates.

* `IsResiduallyFinite.of_injective`, `IsResiduallyFinite.prod` — the two
  closure properties used in Proposition 41.1: the exact quotient embeds in a
  product of two residually finite groups, hence is residually finite.
* `finiteResidual_le_ker` — a homomorphism onto a residually finite target
  cannot hide anything from finite quotients of the source.
* `three_radicals_eq` — **Theorem 41.2**.  If the MF radical *contains* the
  kernel of some homomorphism to a residually finite group, then that kernel is
  simultaneously all three radicals.  Only one inclusion is assumed: the chain
  supplies the other three, so an exactness computation on the MF side is
  enough to pin down the finite residual as well.
-/

namespace GroupApproximation

open MatricialStabilityRadical

universe u v w

variable {G : Type u} [Group G] {P : Type v} [Group P] {Q : Type w} [Group Q]

/-- A homomorphism into a residually finite group cannot hide anything from the
finite quotients of its source: the finite residual lands in the kernel. -/
theorem finiteResidual_le_ker (f : G →* P) (hP : IsResiduallyFinite P) :
    finiteResidual G ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmap : f x ∈ (finiteResidual G).map f := Subgroup.mem_map_of_mem f hx
  have : f x ∈ finiteResidual P := map_finiteResidual_le f hmap
  rw [hP, Subgroup.mem_bot] at this
  exact this

/-- Residual finiteness pulls back along injective homomorphisms.  This is the
"every subgroup of a residually finite group is residually finite" step of
Proposition 41.1, in the form used for an embedding. -/
theorem IsResiduallyFinite.of_injective (f : G →* P) (hf : Function.Injective f)
    (hP : IsResiduallyFinite P) : IsResiduallyFinite G := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hker : x ∈ f.ker := finiteResidual_le_ker f hP hx
  rw [MonoidHom.mem_ker] at hker
  exact hf (by rw [hker, map_one])

/-- A product of two residually finite groups is residually finite. -/
theorem IsResiduallyFinite.prod (hP : IsResiduallyFinite P)
    (hQ : IsResiduallyFinite Q) : IsResiduallyFinite (P × Q) := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : x.1 = 1 := by
    have := finiteResidual_le_ker (MonoidHom.fst P Q) hP hx
    rwa [MonoidHom.mem_ker] at this
  have h2 : x.2 = 1 := by
    have := finiteResidual_le_ker (MonoidHom.snd P Q) hQ hx
    rwa [MonoidHom.mem_ker] at this
  exact Prod.ext h1 h2

/-- **Proposition 41.1**, abstract form.  A group embedding into a product of
two residually finite groups is residually finite.  In the dossier the
embedding is `P ↪ G_* × L_A` of (37.21). -/
theorem isResiduallyFinite_of_embed_prod (f : G →* P × Q)
    (hf : Function.Injective f) (hP : IsResiduallyFinite P)
    (hQ : IsResiduallyFinite Q) : IsResiduallyFinite G :=
  IsResiduallyFinite.of_injective f hf (hP.prod hQ)

/-- **Theorem 41.2.**  Suppose some homomorphism `Φ` to a residually finite
group has kernel inside the MF radical.  Then the MF radical, the
finite-dimensional unitary residual, the finite residual, and `ker Φ` all
coincide.

The single assumed inclusion is the exactness computation; the reverse
inclusions travel around the chain `Res_MF ≤ Rad_fd ≤ Res_fin ≤ ker Φ`. -/
theorem three_radicals_eq (Φ : G →* P) (hP : IsResiduallyFinite P)
    (hMF : Φ.ker ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G = fdUnitaryResidual G ∧
      fdUnitaryResidual G = finiteResidual G ∧
      finiteResidual G = Φ.ker := by
  have h1 : actualCoronaMFResidual G ≤ fdUnitaryResidual G :=
    actualCoronaMFResidual_le_fdUnitaryResidual
  have h2 : fdUnitaryResidual G ≤ finiteResidual G :=
    fdUnitaryResidual_le_finiteResidual
  have h3 : finiteResidual G ≤ Φ.ker := finiteResidual_le_ker Φ hP
  exact ⟨le_antisymm h1 (h2.trans (h3.trans hMF)),
    le_antisymm h2 (h3.trans (hMF.trans h1)),
    le_antisymm h3 (hMF.trans (h1.trans h2))⟩

/-- The same conclusion phrased as a single chain of equalities against the
kernel: everything invisible to finite quotients is already invisible to the
MF machinery, and conversely. -/
theorem actualCoronaMFResidual_eq_finiteResidual (Φ : G →* P)
    (hP : IsResiduallyFinite P) (hMF : Φ.ker ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G = finiteResidual G :=
  (three_radicals_eq Φ hP hMF).1.trans (three_radicals_eq Φ hP hMF).2.1

end GroupApproximation
