import GroupApproximation.GGT.OsinTheorem54Lemma24

/-!
# Theorem 5.4 for a family of peripheral subgroups

Osin's Theorem 5.4 is stated for *a finite collection* `{H_λ}_{λ∈Λ}`.  The
repository's `GGT.OsinTheorem54` fixes `Λ = Unit`, which is the case its own
consumer (`(AH₄) ⇒ (AH₁)`, a single hyperbolically embedded subgroup) needs.
Other consumers do not: a relator-separation argument that cones off two
subgroups at once works at `Λ = Bool`, and no amount of the `Unit` statement
gives it.

This module states the theorem at a general index type and reproves the
reduction to the separating-coset data there.

## What is and is not an instance of what

`OsinTheorem54Fam` implies `OsinTheorem54` (`osinTheorem54_of_fam`) and
`SepDataStatementFam` implies `SepDataStatement`
(`sepDataStatement_of_sepDataStatementFam`), both by taking `Λ = Unit`.

**The converse directions are not available, and this is not an oversight.**  A
`RelGenSet G Bool` is not a `RelGenSet G Unit`: its alphabet cones off two
subgroups, its two relative metrics `d̂_true` and `d̂_false` are different
functions, and the enlargement `Y` produced for one of them is not the one
produced for the other.  Nothing in the `Unit` statement quantifies over that
situation.  So the `Unit` version is an instance of this one in one direction
only, and a consumer at `Λ = Bool` has to be served from here.

## Where the finiteness of `Λ` is spent

`[Finite Λ]` is Osin's own hypothesis ("a finite collection of subgroups").
It is not used by the reduction below, which runs one `λ` at a time; it is
carried because the separating-coset construction that inhabits
`SepDataStatementFam` needs it --- concretely, at `finite_base_asymmetry'`,
where the letters of `X` whose inverse is not a letter are spread over the
`H_λ` and must be finite in total.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **Osin's separating-coset data for `↪_h (G,X)`, at a general family.**  The
fields are those of `SepData`, one per cited lemma of *Acylindrically hyperbolic
groups* §4–§5, with the index type left free.

Only `sep` --- the count `|S(f,g;D)|` --- is insensitive to `Λ`; the family
enters through `enlarged`, whose relative metrics are indexed by `Λ`, and
through `emb`, which asserts local finiteness of every one of them. -/
structure SepDataFam {G : Type u} [Group G] {Λ : Type w} (D : RelGenSet G Λ) where
  /-- `|S(f,g;D)|`, the number of `(f,g;D)`-separating cosets (Definition 4.3). -/
  sep : G → G → ℕ
  /-- The relative generating set on Osin's `Y`, over the same family. -/
  enlarged : RelGenSet G Λ
  /-- `X ⊆ Y`, the first half of Lemma 5.6. -/
  base_subset : D.base ⊆ enlarged.base
  /-- The family is untouched by the enlargement. -/
  fam_eq : enlarged.fam = D.fam
  /-- Lemma 5.6 and Lemma 5.8: clause (a) of Theorem 5.4. -/
  emb : enlarged.IsHyperbolicallyEmbedded
  /-- No geodesic from `f` to itself penetrates a coset essentially. -/
  sep_self : ∀ f : G, sep f f = 0
  /-- `S(f,g;D) = S(g,f;D)`: reversing a geodesic reverses the penetrations. -/
  sep_comm : ∀ f g : G, sep f g = sep g f
  /-- **Osin, Lemma 4.9**: a triangle inequality with defect two. -/
  sep_triangle : ∀ f g h : G, sep f g ≤ sep f h + sep g h + 2
  /-- Left translation carries separating cosets to separating cosets. -/
  sep_smul : ∀ a f g : G, sep (a * f) (a * g) = sep f g
  /-- **Osin, Lemma 5.10**, left half. -/
  dist_le_sep : ∀ f g : G,
    wordDist enlarged.alphabet.carrier f g ≤ 2 * sep f g + 1
  /-- **Osin, Lemma 5.10**, right half. -/
  sep_le_dist : ∀ f g : G,
    sep f g ≤ 3 * wordDist enlarged.alphabet.carrier f g

namespace SepDataFam

section Core

variable {G : Type u} [Group G] {Λ : Type w} {D : RelGenSet G Λ}
  (S : SepDataFam D)

/-- Osin's `Y` contains the identity. -/
theorem sep_one_one : S.sep 1 1 = 0 := S.sep_self 1

/-- `|S(1,y⁻¹;D)| = |S(1,y;D)|`, so Osin's `Y` is symmetric. -/
theorem sep_one_inv (y : G) : S.sep 1 y⁻¹ = S.sep 1 y := by
  have h1 : S.sep (y * 1) (y * y⁻¹) = S.sep 1 y⁻¹ := S.sep_smul y 1 y⁻¹
  rw [mul_one, mul_inv_cancel] at h1
  rw [← h1, S.sep_comm]

/-- **Osin's Lemma 5.11 with the geometry removed**, at a general family, in
the exact-distance form his proof establishes.  Word for word the `Unit`
statement `SepData.AcylindricalCore`: the count is taken in the enlarged word
metric, which does not see the index type. -/
def AcylindricalCore : Prop :=
  ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
    wordDist S.enlarged.alphabet.carrier 1 z = R →
      {k : G | wordDist S.enlarged.alphabet.carrier 1 k ≤ m ∧
          wordDist S.enlarged.alphabet.carrier 1 (z⁻¹ * k * z) ≤ m}.Finite ∧
        {k : G | wordDist S.enlarged.alphabet.carrier 1 k ≤ m ∧
          wordDist S.enlarged.alphabet.carrier 1
            (z⁻¹ * k * z) ≤ m}.ncard ≤ N

/-- **Clause (b) of Theorem 5.4 from the residue, at a general family.**

`isAcylindrical_cayley_of_exactCore` is Lemma 2.4 in the direction the chain
uses it, proved rather than cited, and it never looks at the index type: it
argues on the Cayley graph of the enlarged alphabet alone.  So this is the
`Unit` proof unchanged. -/
theorem isAcylindrical_of_core (hcore : S.AcylindricalCore) :
    IsAcylindrical G (Cayley S.enlarged.alphabet) := by
  obtain ⟨δ, hδ⟩ := S.emb.hyperbolic
  exact isAcylindrical_cayley_of_exactCore S.enlarged.alphabet hδ hcore

end Core

end SepDataFam

section UnitInstance

variable {G : Type u} [Group G]

/-- **A one-element family is a family.**  The two structures have the same
fields, so the `Unit` data of `GGT/OsinSeparatingCosets.lean` is recovered from
the general data by forgetting nothing at all.

There is no map back.  A `SepDataFam` over `Λ = Bool` carries an `enlarged`
relative generating set with two coned-off subgroups and two relative metrics,
and `SepData` has no room for it. -/
def SepDataFam.toSepData {D : RelGenSet G Unit} (S : SepDataFam D) : SepData D where
  sep := S.sep
  enlarged := S.enlarged
  base_subset := S.base_subset
  fam_eq := S.fam_eq
  emb := S.emb
  sep_self := S.sep_self
  sep_comm := S.sep_comm
  sep_triangle := S.sep_triangle
  sep_smul := S.sep_smul
  dist_le_sep := S.dist_le_sep
  sep_le_dist := S.sep_le_dist

end UnitInstance

/-- **The remaining input of Theorem 5.4 at a general family**, in the shape
Osin's §4–§5 delivers it.  `[Finite Λ]` is his hypothesis on the collection. -/
def SepDataStatementFam : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) [Finite Λ] (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → ∃ S : SepDataFam D, S.AcylindricalCore

/-- **Osin, *Acylindrically hyperbolic groups*, Theorem 5.4**, at the index type
the source states it for:

> Let `G` be a group, `{H_λ}_{λ∈Λ}` a finite collection of subgroups of `G`,
> `X` a subset of `G`.  Suppose that `{H_λ}_{λ∈Λ} ↪_h (G,X)`.  Then there
> exists `Y ⊆ G` such that `X ⊆ Y` and the following conditions hold.
> (a) `{H_λ}_{λ∈Λ} ↪_h (G,Y)`.  In particular, the Cayley graph
>     `Γ(G, Y ⊔ H)` is hyperbolic.
> (b) The action of `G` on `Γ(G, Y ⊔ H)` is acylindrical.

`GGT.OsinTheorem54` is this with `Λ = Unit`, which is all `(AH₄) ⇒ (AH₁)`
consumes; the enlargement `Y` is still necessary there, for the reason recorded
at that declaration. -/
def OsinTheorem54Fam : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) [Finite Λ] (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∃ D' : RelGenSet G Λ, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
        D'.IsHyperbolicallyEmbedded ∧ IsAcylindrical G (Cayley D'.alphabet)

/-- **Theorem 5.4 at a general family from the separating-coset data alone.**

The `Unit` reduction `osinTheorem54_of_sepDataStatement` transports without a
change of argument: clause (a) is a field of the data, and clause (b) is
`SepDataFam.isAcylindrical_of_core`, whose only geometric input is the proved
Lemma 2.4 on the Cayley graph of the enlarged alphabet.  Nothing in the
reduction inspects `Λ`, and in particular nothing in it uses `[Finite Λ]`. -/
theorem osinTheorem54Fam_of_sepDataStatementFam
    (h : SepDataStatementFam.{u, w}) : OsinTheorem54Fam.{u, w} := by
  intro G _inst Λ _fin D hD
  obtain ⟨S, hcore⟩ := h G Λ D hD
  exact ⟨S.enlarged, S.base_subset, S.fam_eq, S.emb,
    S.isAcylindrical_of_core hcore⟩

/-- **The `Unit` input is an instance of the general one.**  Take `Λ = Unit` and
forget nothing. -/
theorem sepDataStatement_of_sepDataStatementFam
    (h : SepDataStatementFam.{u, 0}) : SepDataStatement.{u} := by
  intro G _inst D hD
  obtain ⟨S, hcore⟩ := h G Unit D hD
  exact ⟨S.toSepData, hcore⟩

/-- **The `Unit` theorem is an instance of the general one.**  In this direction
only: see the note on `SepDataFam.toSepData`. -/
theorem osinTheorem54_of_fam (h : OsinTheorem54Fam.{u, 0}) :
    OsinTheorem54.{u} := by
  intro G _inst D hD
  exact h G Unit D hD

end OsinEnlargement
end GGT
end GroupApproximation
