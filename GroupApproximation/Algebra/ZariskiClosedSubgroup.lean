import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Nullstellensatz

/-!
# Zariski closed subgroups of `GL(V)`

The manuscript's envelope remark — `non_mf_groups_exist.tex`,
`\begin{remark}[chain conditions suffice]` inside
`\section{The finite-dimensional obstruction}` (`\ref{sec:findim}`) — took the
invariant of a subgroup to be *the
Zariski closure of its image in* `GL(V)`, and appealed to the classical fact
that

> the closed subgroups of `GL(V)` in the Zariski topology satisfy the
> descending chain condition,

which the badge on `Criterion/ClosedEnvelopeCompression` quantifies over rather
than proves.  This file supplies the missing side of that badge: it defines the
Zariski topology on `GL(V)` concretely and develops exactly the closure
operations that the chain condition (proved in
`Algebra/ZariskiDescendingChain`) and the envelope deduction need.

**The remark is no longer printed.**  Commit `3a45fa60` ("Editorial pass:
rewrite orbit collapse, cut what nothing uses") deleted it along with the other
passages nothing consumed; the manuscript now says nothing about Zariski
envelopes or chain conditions.  The mathematics below is unaffected and stands
on its own, but it no longer discharges a printed claim, so no badge is owed
and none should be added on its account.

## The definition

`GL(V)` is realised as `Matrix.GeneralLinearGroup n k`, the units of the
`n × n` matrix ring over a field `k` — that is, `GL(V)` for `V = n → k`, which
is `GL(V)` for an arbitrary `V` of dimension `#n` once a basis is fixed.  The
Zariski topology on `GL n k` is the subspace topology inherited from the affine
space `Matrix n n k = 𝔸^(n × n)`, so a subset is **closed** exactly when it is
the set of invertible matrices whose entries satisfy a family of polynomial
equations.  `IsZClosed` says precisely that: `T` is the preimage, under the
entry-coordinate map `coords`, of the zero locus of an ideal of `k[X_{ij}]`.
No localisation at `det` is needed, because closed subsets of a subspace are
the traces of closed subsets of the ambient space.

## What is proved here

* `zIdeal`/`zClosure`: the ideal–variety Galois pair for `GL n k`, obtained by
  transporting `MvPolynomial.vanishingIdeal` and `MvPolynomial.zeroLocus` along
  `coords`.  The key facts are `preimage_zeroLocus_zIdeal` (a closed set is
  recovered from its ideal) and `subset_of_zIdeal_le` (the pair reflects
  inclusions), which together make `zIdeal` an order-reversing embedding of the
  closed sets into the ideals — the engine of the chain condition.
* `isZClosed_iInter`: arbitrary intersections of closed sets are closed.
* `mulSubst`/`mulSubstHom`: the *linear* substitution realising `M ↦ U * M * V`
  on entry coordinates.  Because left and right multiplication by a fixed
  matrix is linear in the entries — no determinants, no denominators — this one
  construction proves that closed sets are stable under every two-sided
  translation `y ↦ u * y * v` (`isZClosed_translate`), and in particular under
  conjugation (`isZClosedSubgroup_map_conj`), which is the conjugation
  stability the envelope deduction assumes.
* `zEnvelope`: the algebraic envelope of a subgroup, i.e. the smallest Zariski
  closed subgroup containing it, together with its monotonicity and
  conjugation equivariance.  `Algebra/ZariskiDescendingChain` identifies it
  with the topological Zariski closure `zClosure`.

Nothing in this file is conditional: every statement is proved from Mathlib.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace ZariskiClosedSubgroup

open Matrix

/-! ### Conjugation as a bijection of the subgroup lattice

Two bookkeeping identities, used to turn a one-sided statement about
conjugation into a two-sided one.  They are the same computation as in
`Criterion/ClosedEnvelopeCompression`, repeated here so that this file depends
only on Mathlib.
-/

section ConjGroup

variable {G : Type*} [Group G]

/-- Conjugating by `g` and then by `g⁻¹` returns a subgroup to itself. -/
theorem map_conj_map_conj_inv (g : G) (K : Subgroup G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have hcomp : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom)
      = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

/-- Conjugating by `g⁻¹` and then by `g` returns a subgroup to itself. -/
theorem map_conj_inv_map_conj (g : G) (K : Subgroup G) :
    (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have hcomp : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom)
      = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

end ConjGroup

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-! ### Entry coordinates -/

/-- The entry coordinates of a matrix, viewed as a point of the affine space
`(n × n) → k` whose coordinate ring is the polynomial ring `k[X_{ij}]`. -/
def matCoords (M : Matrix n n k) : n × n → k := fun p => M p.1 p.2

omit [Fintype n] [DecidableEq n] [Field k] in
@[simp]
theorem matCoords_apply (M : Matrix n n k) (p : n × n) : matCoords M p = M p.1 p.2 := rfl

/-- The entry coordinates of an invertible matrix.  This is the inclusion of
`GL n k` into the affine space `𝔸^(n × n)` whose subspace topology is the
Zariski topology of `GL n k`. -/
def coords (g : GeneralLinearGroup n k) : n × n → k := matCoords g.val

/-! ### Closed subsets and the ideal–variety pair -/

/-- **Zariski closed subsets of `GL(V)`.**  A subset of `GL n k` is closed when
it is cut out, inside `GL n k`, by polynomial equations in the matrix entries:
it is the trace on `GL n k` of the zero locus of an ideal of `k[X_{ij}]`.  This
is the subspace topology `GL n k` inherits from the affine space of all
matrices. -/
def IsZClosed (T : Set (GeneralLinearGroup n k)) : Prop :=
  ∃ I : Ideal (MvPolynomial (n × n) k), T = coords ⁻¹' MvPolynomial.zeroLocus k I

/-- The ideal of all polynomial relations satisfied by the entries of every
element of `T`. -/
def zIdeal (T : Set (GeneralLinearGroup n k)) : Ideal (MvPolynomial (n × n) k) :=
  MvPolynomial.vanishingIdeal k (coords '' T)

/-- Membership in `zIdeal` is vanishing at every point of the set. -/
theorem mem_zIdeal {T : Set (GeneralLinearGroup n k)} {f : MvPolynomial (n × n) k} :
    f ∈ zIdeal T ↔ ∀ g ∈ T, MvPolynomial.aeval (coords g) f = 0 := by
  constructor
  · intro hf g hg
    exact hf (coords g) ⟨g, hg, rfl⟩
  · intro hf c hc
    obtain ⟨g, hg, rfl⟩ := hc
    exact hf g hg

/-- Taking relations is order reversing. -/
theorem zIdeal_antitone {T T' : Set (GeneralLinearGroup n k)} (h : T ⊆ T') :
    zIdeal T' ≤ zIdeal T :=
  MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono h)

/-- Every set is contained in the zero locus of its own relations. -/
theorem subset_zeroLocus_zIdeal (T : Set (GeneralLinearGroup n k)) :
    T ⊆ coords ⁻¹' MvPolynomial.zeroLocus k (zIdeal T) := by
  intro g hg
  exact MvPolynomial.zeroLocus_vanishingIdeal_le (k := k) (coords '' T) ⟨g, hg, rfl⟩

/-- Any ideal cutting out `T` is contained in the full ideal of relations. -/
theorem le_zIdeal_of_eq {T : Set (GeneralLinearGroup n k)}
    {I : Ideal (MvPolynomial (n × n) k)}
    (h : T = coords ⁻¹' MvPolynomial.zeroLocus k I) : I ≤ zIdeal T := by
  intro f hf
  rw [mem_zIdeal]
  intro g hg
  rw [h, Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff] at hg
  exact hg f hf

/-- **A closed set is recovered from its ideal of relations.**  This is the
half of the ideal–variety correspondence that needs `T` to be closed, and it is
what makes `zIdeal` injective on closed sets. -/
theorem preimage_zeroLocus_zIdeal {T : Set (GeneralLinearGroup n k)} (hT : IsZClosed T) :
    coords ⁻¹' MvPolynomial.zeroLocus k (zIdeal T) = T := by
  obtain ⟨I, hI⟩ := hT
  refine Set.Subset.antisymm ?_ (subset_zeroLocus_zIdeal T)
  have hle : I ≤ zIdeal T := le_zIdeal_of_eq hI
  intro g hg
  rw [hI]
  exact MvPolynomial.zeroLocus_anti_mono hle hg

/-- **The correspondence reflects inclusions.**  If `T` is closed and its
relations are contained in those of `T'`, then `T'` is contained in `T`. -/
theorem subset_of_zIdeal_le {T T' : Set (GeneralLinearGroup n k)} (hT : IsZClosed T)
    (h : zIdeal T ≤ zIdeal T') : T' ⊆ T := by
  intro g hg
  rw [← preimage_zeroLocus_zIdeal hT]
  exact MvPolynomial.zeroLocus_anti_mono h (subset_zeroLocus_zIdeal T' hg)

/-! ### The closure operator -/

/-- The Zariski closure of a subset of `GL n k`: the zero locus of all
polynomial relations satisfied on it. -/
def zClosure (T : Set (GeneralLinearGroup n k)) : Set (GeneralLinearGroup n k) :=
  coords ⁻¹' MvPolynomial.zeroLocus k (zIdeal T)

/-- The closure is closed. -/
theorem isZClosed_zClosure (T : Set (GeneralLinearGroup n k)) : IsZClosed (zClosure T) :=
  ⟨zIdeal T, rfl⟩

/-- A set is contained in its closure. -/
theorem subset_zClosure (T : Set (GeneralLinearGroup n k)) : T ⊆ zClosure T :=
  subset_zeroLocus_zIdeal T

/-- A closed set is its own closure. -/
theorem zClosure_eq_self {T : Set (GeneralLinearGroup n k)} (hT : IsZClosed T) :
    zClosure T = T :=
  preimage_zeroLocus_zIdeal hT

/-- The closure is monotone. -/
theorem zClosure_mono {T T' : Set (GeneralLinearGroup n k)} (h : T ⊆ T') :
    zClosure T ⊆ zClosure T' := by
  intro y hy
  exact MvPolynomial.zeroLocus_anti_mono (zIdeal_antitone h) hy

/-- **The closure is the smallest closed superset.** -/
theorem zClosure_subset_of_isZClosed {T S : Set (GeneralLinearGroup n k)} (hS : IsZClosed S)
    (h : T ⊆ S) : zClosure T ⊆ S := by
  have h1 : zClosure T ⊆ zClosure S := zClosure_mono h
  rw [zClosure_eq_self hS] at h1
  exact h1

/-! ### Stability of closedness under intersections -/

omit [Fintype n] [DecidableEq n] in
/-- A point lies in the zero locus of `I` exactly when `I` consists of
polynomials vanishing at that point. -/
theorem mem_zeroLocus_iff_le_vanishingIdeal (c : n × n → k)
    (I : Ideal (MvPolynomial (n × n) k)) :
    c ∈ MvPolynomial.zeroLocus k I ↔
      I ≤ MvPolynomial.vanishingIdeal k ({c} : Set (n × n → k)) := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff c p).2 (h p hp)
  · intro h p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff c p).1 (h hp)

/-- **Arbitrary intersections of closed sets are closed**: the intersection of
the zero loci of a family of ideals is the zero locus of their supremum. -/
theorem isZClosed_iInter {ι : Sort*} {T : ι → Set (GeneralLinearGroup n k)}
    (hT : ∀ i, IsZClosed (T i)) : IsZClosed (⋂ i, T i) := by
  choose I hI using hT
  refine ⟨⨆ i, I i, ?_⟩
  ext y
  simp only [Set.mem_iInter, Set.mem_preimage]
  rw [mem_zeroLocus_iff_le_vanishingIdeal, iSup_le_iff]
  constructor
  · intro h i
    have hy := h i
    rw [hI i, Set.mem_preimage, mem_zeroLocus_iff_le_vanishingIdeal] at hy
    exact hy
  · intro h i
    rw [hI i, Set.mem_preimage, mem_zeroLocus_iff_le_vanishingIdeal]
    exact h i

/-- The whole of `GL n k` is closed. -/
theorem isZClosed_univ : IsZClosed (Set.univ : Set (GeneralLinearGroup n k)) := by
  refine ⟨⊥, ?_⟩
  rw [MvPolynomial.zeroLocus_bot]
  simp

/-! ### Linear substitutions and two-sided translations

Left and right multiplication by fixed matrices is *linear* in the entries, so
it is realised by substituting linear forms into the coordinate ring.  This is
the only geometry the envelope argument needs: no determinant, no localisation.
-/

/-- The linear form whose value at the entries of `M` is the `(i, b)` entry of
`U * M`. -/
def rowForm (U : Matrix n n k) (i b : n) : MvPolynomial (n × n) k :=
  ∑ a : n, MvPolynomial.C (U i a) * MvPolynomial.X ((a, b) : n × n)

omit [DecidableEq n] in
/-- `rowForm` computes the entries of `U * M`. -/
theorem aeval_rowForm (U M : Matrix n n k) (i b : n) :
    MvPolynomial.aeval (matCoords M) (rowForm U i b) = (U * M) i b := by
  simp only [rowForm, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self_apply, matCoords_apply, Matrix.mul_apply]

/-- The tuple of linear forms realising the substitution `M ↦ U * M * V` on
entry coordinates. -/
def mulSubst (U V : Matrix n n k) (p : n × n) : MvPolynomial (n × n) k :=
  ∑ b : n, rowForm U p.1 b * MvPolynomial.C (V b p.2)

omit [DecidableEq n] in
/-- `mulSubst` computes the entries of `U * M * V`. -/
theorem aeval_mulSubst (U V M : Matrix n n k) (p : n × n) :
    MvPolynomial.aeval (matCoords M) (mulSubst U V p) = matCoords (U * M * V) p := by
  simp only [mulSubst, map_sum, map_mul, aeval_rowForm, MvPolynomial.aeval_C,
    Algebra.algebraMap_self_apply, matCoords_apply, Matrix.mul_apply]

/-- Substitution along `M ↦ U * M * V`, as an endomorphism of the coordinate
ring. -/
def mulSubstHom (U V : Matrix n n k) :
    MvPolynomial (n × n) k →ₐ[k] MvPolynomial (n × n) k :=
  MvPolynomial.bind₁ (mulSubst U V)

omit [DecidableEq n] in
/-- Substituting and then evaluating at `M` is evaluating at `U * M * V`. -/
theorem aeval_mulSubstHom (U V M : Matrix n n k) (f : MvPolynomial (n × n) k) :
    MvPolynomial.aeval (matCoords M) (mulSubstHom U V f)
      = MvPolynomial.aeval (matCoords (U * M * V)) f := by
  have h : (fun p : n × n => MvPolynomial.aeval (matCoords M) (mulSubst U V p))
      = matCoords (U * M * V) := funext fun p => aeval_mulSubst U V M p
  show MvPolynomial.aeval (matCoords M) (MvPolynomial.bind₁ (mulSubst U V) f) = _
  rw [MvPolynomial.aeval_bind₁, h]

/-- The group-level form of `aeval_mulSubstHom`. -/
theorem aeval_mulSubstHom_coords (u v y : GeneralLinearGroup n k)
    (f : MvPolynomial (n × n) k) :
    MvPolynomial.aeval (coords y) (mulSubstHom u.val v.val f)
      = MvPolynomial.aeval (coords (u * y * v)) f := by
  have h := aeval_mulSubstHom u.val v.val y.val f
  simpa only [coords, Units.val_mul] using h

omit [Fintype n] [DecidableEq n] in
/-- A point lies in the zero locus of a pushed-forward ideal exactly when the
substituted generators vanish there. -/
theorem mem_zeroLocus_map_iff (φ : MvPolynomial (n × n) k →ₐ[k] MvPolynomial (n × n) k)
    (I : Ideal (MvPolynomial (n × n) k)) (c : n × n → k) :
    c ∈ MvPolynomial.zeroLocus k (Ideal.map φ I) ↔
      ∀ p ∈ I, MvPolynomial.aeval c (φ p) = 0 := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    exact h (φ p) (Ideal.mem_map_of_mem _ hp)
  · intro h q hq
    have hle : Ideal.map φ I ≤ MvPolynomial.vanishingIdeal k ({c} : Set (n × n → k)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap]
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff c (φ p)).2 (h p hp)
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff c q).1 (hle hq)

/-- The two-sided translation `y ↦ u * y * v`, as a preimage operation on
subsets of `GL n k`. -/
def translate (u v : GeneralLinearGroup n k) (T : Set (GeneralLinearGroup n k)) :
    Set (GeneralLinearGroup n k) := {y | u * y * v ∈ T}

/-- **Closed sets are stable under two-sided translation.**  Translation is a
linear change of the entry coordinates, so it pulls polynomial equations back
to polynomial equations. -/
theorem isZClosed_translate {T : Set (GeneralLinearGroup n k)} (hT : IsZClosed T)
    (u v : GeneralLinearGroup n k) : IsZClosed (translate u v T) := by
  obtain ⟨I, rfl⟩ := hT
  refine ⟨Ideal.map (mulSubstHom u.val v.val) I, ?_⟩
  ext y
  have hmemL : (y ∈ translate u v (coords ⁻¹' MvPolynomial.zeroLocus k I))
      ↔ ∀ p ∈ I, MvPolynomial.aeval (coords (u * y * v)) p = 0 := Iff.rfl
  rw [hmemL, Set.mem_preimage, mem_zeroLocus_map_iff]
  constructor
  · intro h p hp
    rw [aeval_mulSubstHom_coords]
    exact h p hp
  · intro h p hp
    have hp' := h p hp
    rw [aeval_mulSubstHom_coords] at hp'
    exact hp'

/-! ### Closed subgroups -/

/-- **A Zariski closed subgroup of `GL(V)`**: a subgroup whose underlying set is
Zariski closed. -/
def IsZClosedSubgroup (H : Subgroup (GeneralLinearGroup n k)) : Prop :=
  IsZClosed (H : Set (GeneralLinearGroup n k))

/-- `GL n k` is a closed subgroup of itself. -/
theorem isZClosedSubgroup_top :
    IsZClosedSubgroup (⊤ : Subgroup (GeneralLinearGroup n k)) := by
  have h : IsZClosed ((⊤ : Subgroup (GeneralLinearGroup n k)) :
      Set (GeneralLinearGroup n k)) := by
    rw [Subgroup.coe_top]
    exact isZClosed_univ
  exact h

/-- **Closedness is conjugation stable.**  Conjugation by a fixed element is a
two-sided translation, hence a linear change of coordinates. -/
theorem isZClosedSubgroup_map_conj {H : Subgroup (GeneralLinearGroup n k)}
    (hH : IsZClosedSubgroup H) (g : GeneralLinearGroup n k) :
    IsZClosedSubgroup (H.map (MulAut.conj g).toMonoidHom) := by
  have hset : ((H.map (MulAut.conj g).toMonoidHom : Subgroup (GeneralLinearGroup n k)) :
      Set (GeneralLinearGroup n k))
      = translate g⁻¹ g (H : Set (GeneralLinearGroup n k)) := by
    ext y
    simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, translate,
      Set.mem_setOf_eq]
  have hcl : IsZClosed (translate g⁻¹ g (H : Set (GeneralLinearGroup n k))) :=
    isZClosed_translate hH g⁻¹ g
  rw [← hset] at hcl
  exact hcl

/-- An arbitrary infimum of closed subgroups is closed. -/
theorem isZClosedSubgroup_sInf {𝒮 : Set (Subgroup (GeneralLinearGroup n k))}
    (h𝒮 : ∀ H ∈ 𝒮, IsZClosedSubgroup H) : IsZClosedSubgroup (sInf 𝒮) := by
  have h : IsZClosed ((sInf 𝒮 : Subgroup (GeneralLinearGroup n k)) :
      Set (GeneralLinearGroup n k)) := by
    rw [Subgroup.coe_sInf]
    exact isZClosed_iInter fun H => isZClosed_iInter fun hH => h𝒮 H hH
  exact h

/-! ### The algebraic envelope -/

/-- **The algebraic envelope of a subgroup of `GL(V)`**: the smallest Zariski
closed subgroup containing it.  `Algebra/ZariskiDescendingChain` shows this
coincides with the topological Zariski closure. -/
def zEnvelope (H : Subgroup (GeneralLinearGroup n k)) : Subgroup (GeneralLinearGroup n k) :=
  sInf {K : Subgroup (GeneralLinearGroup n k) | IsZClosedSubgroup K ∧ H ≤ K}

/-- The envelope is closed. -/
theorem isZClosedSubgroup_zEnvelope (H : Subgroup (GeneralLinearGroup n k)) :
    IsZClosedSubgroup (zEnvelope H) :=
  isZClosedSubgroup_sInf fun _ hK => hK.1

/-- The envelope contains the subgroup. -/
theorem le_zEnvelope (H : Subgroup (GeneralLinearGroup n k)) : H ≤ zEnvelope H :=
  le_sInf fun _ hK => hK.2

/-- The envelope is the least closed subgroup containing the subgroup. -/
theorem zEnvelope_le {H K : Subgroup (GeneralLinearGroup n k)} (hK : IsZClosedSubgroup K)
    (h : H ≤ K) : zEnvelope H ≤ K :=
  sInf_le ⟨hK, h⟩

/-- The envelope is monotone. -/
theorem zEnvelope_mono {H H' : Subgroup (GeneralLinearGroup n k)} (h : H ≤ H') :
    zEnvelope H ≤ zEnvelope H' :=
  zEnvelope_le (isZClosedSubgroup_zEnvelope H') (h.trans (le_zEnvelope H'))

/-- One half of conjugation equivariance of the envelope. -/
theorem zEnvelope_map_conj_le (g : GeneralLinearGroup n k)
    (H : Subgroup (GeneralLinearGroup n k)) :
    zEnvelope (H.map (MulAut.conj g).toMonoidHom)
      ≤ (zEnvelope H).map (MulAut.conj g).toMonoidHom :=
  zEnvelope_le (isZClosedSubgroup_map_conj (isZClosedSubgroup_zEnvelope H) g)
    (Subgroup.map_mono (le_zEnvelope H))

/-- **The envelope is conjugation equivariant.** -/
theorem zEnvelope_map_conj (g : GeneralLinearGroup n k)
    (H : Subgroup (GeneralLinearGroup n k)) :
    zEnvelope (H.map (MulAut.conj g).toMonoidHom)
      = (zEnvelope H).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm (zEnvelope_map_conj_le g H) ?_
  have h := zEnvelope_map_conj_le g⁻¹ (H.map (MulAut.conj g).toMonoidHom)
  rw [map_conj_map_conj_inv] at h
  have h2 : (zEnvelope H).map (MulAut.conj g).toMonoidHom ≤
      ((zEnvelope (H.map (MulAut.conj g).toMonoidHom)).map
        (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono h
  rwa [map_conj_inv_map_conj] at h2

end

end ZariskiClosedSubgroup
end GroupApproximation
