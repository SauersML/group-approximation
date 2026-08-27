import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# Hyperbolically embedded subgroups (Dahmani--Guirardel--Osin)

This module writes down `{H λ} ↪_h (G, X)` in the form Minasyan--Osin recall it
(*Acylindrical hyperbolicity of groups acting on trees*, §3.1, after
Dahmani--Guirardel--Osin, *Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), Definition 4.25):

> Let `G` be a group, `H ≤ G`, `X ⊆ G`.  Assume `G = ⟨X ∪ H⟩` and denote by
> `Γ(G, X ⊔ H)` the Cayley graph of `G` with respect to the generating set
> `X ⊔ H` (even though `X` and `H` might intersect as subsets of `G`, for the
> purposes of constructing `Γ(G, X ⊔ H)` we consider them to be disjoint) and
> by `Γ_H` the Cayley graph of `H` with respect to the generating set `H`.
> Given `h₁, h₂ ∈ H`, define `d̂(h₁,h₂)` to be the length of a shortest path
> `p` in `Γ(G, X ⊔ H)` that connects `h₁` to `h₂` and does not contain edges
> of `Γ_H`. ... We say that `H` is *hyperbolically embedded* in `G` with
> respect to `X` if
> (a) `G = ⟨X ∪ H⟩` and `Γ(G, X ⊔ H)` is hyperbolic;
> (b) `(H, d̂)` is a locally finite space, i.e. every ball (of finite radius)
> is finite.

## How the two clauses are formalized

* **The Cayley graph.**  Duplicating a letter — which is all the disjointness
  `X ⊔ H` does to the vertex set — creates parallel edges and leaves the
  vertex metric unchanged, so clause (a) is stated against the repository's
  `Manuscript.NonMF.TorsionFree.Cayley` for the alphabet `X ∪ ⋃ λ, H λ`
  taken as a subset of `G`.  Hyperbolicity is Gromov's four-point condition on
  that vertex metric, `HullGeometry.IsHyperbolicSpace`, exactly as in the
  definition of `TorsionFree.IsAcylindricallyHyperbolic`.

* **The relative metric.**  The disjointness *is* needed for `d̂`, because an
  edge of `Γ_{H λ}` is one labelled by a `λ`-letter between two vertices of
  `H λ`, while the same group element used as an `X`-letter labels an edge that
  is not in `Γ_{H λ}`.  So paths are spelled by `RelLetter`s — a letter is an
  `X`-letter or a `λ`-letter — and `AvoidsFrom` is the recursion along the path
  that forbids reading a `λ`-letter at a vertex of `H λ`.  Local finiteness is
  stated as finiteness of the balls about `1`; left translation by an element
  of `H λ` is an automorphism of `Γ(G, X ⊔ ⨆H)` preserving `Γ_{H λ}`, so `d̂_λ`
  is `H λ`-invariant and the balls about `1` control all balls.

* **`d̂` itself is not defined**, only its balls: the definition needs
  `ℕ ∪ {∞}` and every use of it in the sequel is through the balls.

## What is proved

`relBall_zero`, the sanity check that the radius-`0` ball is `{1}`.  Everything
else here is a definition.  The theorems *about* hyperbolically embedded
subgroups — Dahmani--Guirardel--Osin's Theorem 6.8 and Osin's `(AH₄) ⇒ (AH₁)`
— are stated, as named propositions, in `GGT.WPDAcylindricalHyperbolicity`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Letters of the relative alphabet -/

/-- **A letter of `X ⊔ (⨆ λ, H λ)`.**  The disjointness of the union is the
point of this type: the same group element can occur as a `base` letter and as
a `comp` letter, and the two label different edges of `Γ(G, X ⊔ ⨆H)`. -/
inductive RelLetter (G : Type u) (Λ : Type w) where
  /-- A letter of the relative generating set `X`. -/
  | base : G → RelLetter G Λ
  /-- A letter of the `λ`-th subgroup of the family. -/
  | comp : Λ → G → RelLetter G Λ

namespace RelLetter

variable {G : Type u} {Λ : Type w}

/-- The group element a letter names. -/
def val : RelLetter G Λ → G
  | base g => g
  | comp _ h => h

/-- `IsCompOf lam a` holds when `a` is a letter of the `lam`-th subgroup. -/
def IsCompOf (lam : Λ) : RelLetter G Λ → Prop
  | base _ => False
  | comp mu _ => mu = lam

/-- The element spelled by a word: the ordered product of its letters. -/
def listVal (w : List (RelLetter G Λ)) : G := (w.map RelLetter.val).prod

theorem listVal_nil : listVal ([] : List (RelLetter G Λ)) = 1 := rfl

end RelLetter

/-! ## Relative generating sets -/

/-- **A relative generating set** `(X, {H λ})` of `G`: a subset `X` and a
family of subgroups whose union is a symmetric generating set.  This is the
data `↪_h (G, X)` is stated against. -/
structure RelGenSet (G : Type u) [Group G] (Λ : Type w) where
  /-- The relative generating set `X`. -/
  base : Set G
  /-- The family `{H λ}`. -/
  fam : Λ → Subgroup G
  /-- `X ∪ ⋃ H λ` is symmetric and generates `G`; this is
  Dahmani--Guirardel--Osin's `G = ⟨X ∪ H⟩`. -/
  symmetricGenerating :
    IsSymmetricGeneratingSet (base ∪ ⋃ lam : Λ, (fam lam : Set G))

namespace RelGenSet

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The alphabet of `Γ(G, X ⊔ ⨆H)`.**  Its word metric is the vertex metric
of the relative Cayley graph. -/
def alphabet (D : RelGenSet G Λ) : Alphabet G :=
  ⟨D.base ∪ ⋃ lam : Λ, (D.fam lam : Set G), D.symmetricGenerating⟩

/-- An admissible letter: a letter of `X`, or a letter of one of the `H λ`. -/
def IsLetter (D : RelGenSet G Λ) : RelLetter G Λ → Prop
  | RelLetter.base x => x ∈ D.base
  | RelLetter.comp lam h => h ∈ D.fam lam

end RelGenSet

/-- **Paths avoiding `Γ_{H lam}`.**  `AvoidsFrom H lam w v` says that reading
the word `w` from the vertex `v` never traverses an edge of `Γ_{H lam}`: a
`lam`-letter is never read at a vertex lying in `H lam`.  (If the current
vertex `v` lies in `H lam` and the letter is a `lam`-letter, then so does the
next vertex, and the edge between them is an edge of `Γ_{H lam}`.) -/
def AvoidsFrom {G : Type u} [Group G] {Λ : Type w} (H : Λ → Subgroup G)
    (lam : Λ) : List (RelLetter G Λ) → G → Prop
  | [], _ => True
  | a :: w, v =>
      ¬ (RelLetter.IsCompOf lam a ∧ v ∈ H lam) ∧
        AvoidsFrom H lam w (v * a.val)

namespace RelGenSet

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The `d̂_lam`-ball of radius `n` about `1`.**  Its elements are those
`h ∈ H lam` reachable from `1` by a path of length at most `n` in
`Γ(G, X ⊔ ⨆H)` using no edge of `Γ_{H lam}`. -/
def relBall (D : RelGenSet G Λ) (lam : Λ) (n : ℕ) : Set G :=
  {h : G | h ∈ D.fam lam ∧ ∃ w : List (RelLetter G Λ),
    (∀ a ∈ w, D.IsLetter a) ∧ RelLetter.listVal w = h ∧
      AvoidsFrom D.fam lam w 1 ∧ w.length ≤ n}

theorem mem_relBall {D : RelGenSet G Λ} {lam : Λ} {n : ℕ} {h : G} :
    h ∈ D.relBall lam n ↔ h ∈ D.fam lam ∧ ∃ w : List (RelLetter G Λ),
      (∀ a ∈ w, D.IsLetter a) ∧ RelLetter.listVal w = h ∧
        AvoidsFrom D.fam lam w 1 ∧ w.length ≤ n :=
  Iff.rfl

/-- The relative ball of radius `0` is `{1}`: the only path of length `0` is
the empty one. -/
theorem relBall_zero (D : RelGenSet G Λ) (lam : Λ) :
    D.relBall lam 0 = ({1} : Set G) := by
  ext h
  rw [mem_relBall, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, w, -, hval, -, hlen⟩
    rcases w with _ | ⟨a, t⟩
    · rw [← hval, RelLetter.listVal_nil]
    · simp at hlen
  · rintro rfl
    exact ⟨one_mem _, [], by simp, RelLetter.listVal_nil, trivial, by simp⟩

/-- **Hyperbolically embedded family** (Dahmani--Guirardel--Osin,
Definition 4.25): the relative Cayley graph is hyperbolic and every relative
metric is locally finite. -/
structure IsHyperbolicallyEmbedded (D : RelGenSet G Λ) : Prop where
  /-- Clause (a): `Γ(G, X ⊔ ⨆H)` is hyperbolic. -/
  hyperbolic : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet)
  /-- Clause (b): each `(H λ, d̂_λ)` is locally finite. -/
  locallyFinite : ∀ (lam : Λ) (n : ℕ), (D.relBall lam n).Finite

end RelGenSet

/-- **`H ↪_h (G, X)`** for a single subgroup: the one-element family. -/
def IsHypEmbeddedOf (G : Type u) [Group G] (X : Set G) (H : Subgroup G) : Prop :=
  ∃ D : RelGenSet G Unit, D.base = X ∧ D.fam = (fun _ => H) ∧
    D.IsHyperbolicallyEmbedded

/-- **`H ↪_h G`**: hyperbolically embedded with respect to *some* relative
generating set.  This is the notion appearing in Osin's `(AH₄)`. -/
def IsHypEmbedded (G : Type u) [Group G] (H : Subgroup G) : Prop :=
  ∃ X : Set G, IsHypEmbeddedOf G X H

theorem IsHypEmbeddedOf.isHypEmbedded {G : Type u} [Group G] {X : Set G}
    {H : Subgroup G} (h : IsHypEmbeddedOf G X H) : IsHypEmbedded G H :=
  ⟨X, h⟩

end GGT
end GroupApproximation
