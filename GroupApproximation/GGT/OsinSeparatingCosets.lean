import GroupApproximation.GGT.OsinEnlargement

/-!
# Osin's separating cosets, and what Theorem 5.4 actually reduces to

`GGT/OsinEnlargement.lean` left `OsinEnlargementBasepoint` as one opaque leaf.
Reading Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), §4–§5
replaces it by a structure whose fields are individually citable lemmas of that
paper, plus a single residue.

## What the source actually says

The proof of Theorem 5.4 does **not** go through Dahmani--Guirardel--Osin's
isolated-component propositions.  It goes through Osin's own §4, on *separating
cosets*.  Definition 2.8: a path in `Γ(G, X ⊔ ℋ)` is `λ`-admissible when it
contains no edge of `Γ(H_λ, H_λ)`, and `d̂_λ` is the length of a shortest
admissible path (`∞` if there is none) --- which is the metric this repository
already has, as `RelGenSet.relBall`.  Definition 4.3: a path *penetrates*
`xH_λ` when it decomposes as `p₁ a p₂` with `a` an `H_λ`-component; `S(f,g;D)`
is the set of cosets essentially penetrated by a geodesic from `f` to `g` with
`d̂_λ(a₋,a₊) > D`.  Osin fixes `D ≥ 3C` with `C` from Lemma 4.2, and sets

  `Y = {y ∈ G | S(1,y;D) = ∅}`.

The facts about `|S(·,·;D)|` that the proof uses are:

* **Lemma 4.9**: `|S(f,g;D)| ≤ |S(f,h;D)| + |S(g,h;D)| + 2` --- a triangle
  inequality with defect two.
* **Lemma 4.8**: `⪯` linearly orders `S(f,g;D)` and every geodesic penetrates
  the separating cosets in that order.
* **Lemma 5.6**: `X ⊆ Y` and `Γ(G, Y ⊔ ℋ)` is hyperbolic (via Lemma 5.5,
  Breuillard--Cornulier: adding edges preserves hyperbolicity when the added
  edges have uniformly bounded `Σ`-diameter of their `Γ`-geodesics).
* **Lemma 5.8**: `{H_λ} ↪_h (G,Y)` --- clause (a), using Lemma 5.7 of
  Dahmani--Guirardel--Osin (a finite symmetric difference of relative
  generating sets does not change `↪_h`).
* **Lemma 5.9**: consecutive separating cosets are joined by elements of `Y`.
* **Lemma 5.10**: `½(d_{Y⊔ℋ}(f,g) − 1) ≤ |S(f,g;D)| ≤ 3 d_{Y⊔ℋ}(f,g)` ---
  the counting function and the enlarged word metric are quasi-isometric.
* **Lemma 5.11**: `Γ(G, Y ⊔ ℋ)` is acylindrical --- clause (b).

## What this module does

`SepData` bundles exactly those facts, one field per cited lemma, and
`SepData.isAcylindrical_of_core` proves clause (b) from them together with a
single residue, `SepData.AcylindricalCore`.  The bridge is Lemma 5.10 read in
both directions: it converts every hypothesis and conclusion of acylindricity
between the enlarged word metric and the separating-coset count, and
`GGT.OsinEnlargement.isAcylindrical_cayley_of_basepoint` supplies the reduction
to the identity vertex.  So the geometric obligation shrinks to:

> for each `m` there are `R`, `N` such that whenever `|S(1,z;D)| ≥ R`, at most
> `N` elements `k` satisfy `|S(1,k;D)| ≤ m` and `|S(z,kz;D)| ≤ m`.

That is the content of Lemma 5.11, and it is the only part of §5 not reduced to
bookkeeping here.  It is where the linear order of Lemma 4.8 and the local
finiteness of `d̂_λ` do their work: an element almost fixing both ends of a long
chain of separating cosets must almost preserve the chain, and a coset
stabiliser is `d̂`-locally finite.

Nothing in this module inhabits `SepData` or `AcylindricalCore`.  Constructing
the separating cosets themselves needs the component machinery of `Γ(G, X ⊔ ℋ)`,
which this repository does not have.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- **Osin's separating-coset data for `↪_h (G,X)`.**  One field per cited
lemma of *Acylindrically hyperbolic groups* §4–§5, with `sep f g` standing for
`|S(f,g;D)|` and `enlarged` for the relative generating set built on
`Y = {y | S(1,y;D) = ∅}`. -/
structure SepData (D : RelGenSet G Unit) where
  /-- `|S(f,g;D)|`, the number of `(f,g;D)`-separating cosets (Definition 4.3). -/
  sep : G → G → ℕ
  /-- The relative generating set on Osin's `Y`. -/
  enlarged : RelGenSet G Unit
  /-- `X ⊆ Y`, the first half of Lemma 5.6. -/
  base_subset : D.base ⊆ enlarged.base
  /-- The family is untouched by the enlargement. -/
  fam_eq : enlarged.fam = D.fam
  /-- Lemma 5.6 (hyperbolicity of `Γ(G, Y ⊔ ℋ)`) and Lemma 5.8
  (`{H_λ} ↪_h (G,Y)`), which is clause (a) of Theorem 5.4. -/
  emb : enlarged.IsHyperbolicallyEmbedded
  /-- No geodesic from `f` to itself penetrates a coset essentially. -/
  sep_self : ∀ f : G, sep f f = 0
  /-- `S(f,g;D) = S(g,f;D)`: reversing a geodesic reverses the penetrations. -/
  sep_comm : ∀ f g : G, sep f g = sep g f
  /-- **Osin, Lemma 4.9**: a triangle inequality with defect two. -/
  sep_triangle : ∀ f g h : G, sep f g ≤ sep f h + sep g h + 2
  /-- Left translation carries separating cosets to separating cosets. -/
  sep_smul : ∀ a f g : G, sep (a * f) (a * g) = sep f g
  /-- **Osin, Lemma 5.10**, left half: `d_{Y⊔ℋ}(f,g) ≤ 2|S(f,g;D)| + 1`. -/
  dist_le_sep : ∀ f g : G,
    wordDist enlarged.alphabet.carrier f g ≤ 2 * sep f g + 1
  /-- **Osin, Lemma 5.10**, right half: `|S(f,g;D)| ≤ 3 d_{Y⊔ℋ}(f,g)`. -/
  sep_le_dist : ∀ f g : G,
    sep f g ≤ 3 * wordDist enlarged.alphabet.carrier f g

namespace SepData

variable {D : RelGenSet G Unit} (S : SepData D)

/-- Osin's `Y` contains the identity. -/
theorem sep_one_one : S.sep 1 1 = 0 := S.sep_self 1

/-- The separating-coset count of an inverse: `|S(1,y⁻¹;D)| = |S(1,y;D)|`.  So
Osin's `Y` is symmetric, as a relative generating set must be. -/
theorem sep_one_inv (y : G) : S.sep 1 y⁻¹ = S.sep 1 y := by
  have h1 : S.sep (y * 1) (y * y⁻¹) = S.sep 1 y⁻¹ := S.sep_smul y 1 y⁻¹
  rw [mul_one, mul_inv_cancel] at h1
  rw [← h1, S.sep_comm]

/-- **Osin's Lemma 5.11, with the geometry removed.**  The residue: for each
`m` a radius and a bound, in terms of the separating-coset count. -/
def AcylindricalCore : Prop :=
  ∀ m : ℕ, ∃ R N : ℕ, ∀ z : G, R ≤ S.sep 1 z →
    {k : G | S.sep 1 k ≤ m ∧ S.sep z (k * z) ≤ m}.Finite ∧
      {k : G | S.sep 1 k ≤ m ∧ S.sep z (k * z) ≤ m}.ncard ≤ N

/-- **Clause (b) of Theorem 5.4 from the residue.**

Lemma 5.10 converts each hypothesis and each conclusion between the enlarged
word metric and the separating-coset count, and
`isAcylindrical_cayley_of_basepoint` removes the quantifier over the first
vertex. -/
theorem isAcylindrical_of_core (hcore : S.AcylindricalCore) :
    IsAcylindrical G (Cayley S.enlarged.alphabet) := by
  refine isAcylindrical_cayley_of_basepoint S.enlarged.alphabet ?_
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hcore (3 * ⌈ε⌉₊)
  refine ⟨((2 * R + 1 : ℕ) : ℝ), N, ?_⟩
  intro z hz
  -- the hypothesis on `z`, transported by the left half of Lemma 5.10
  have hzd : 2 * R + 1 ≤ wordDist S.enlarged.alphabet.carrier 1 z := by
    exact_mod_cast hz
  have hzs : R ≤ S.sep 1 z := by
    have h := S.dist_le_sep 1 z
    omega
  obtain ⟨hfin, hcard⟩ := hRN z hzs
  -- the two ε-conditions, transported by the right half of Lemma 5.10
  have hsub : {k : G |
        ((wordDist S.enlarged.alphabet.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
        ((wordDist S.enlarged.alphabet.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ) ≤ ε}
      ⊆ {k : G | S.sep 1 k ≤ 3 * ⌈ε⌉₊ ∧ S.sep z (k * z) ≤ 3 * ⌈ε⌉₊} := by
    rintro k ⟨hk1, hk2⟩
    have hc1 : wordDist S.enlarged.alphabet.carrier 1 k ≤ ⌈ε⌉₊ := by
      have h : ((wordDist S.enlarged.alphabet.carrier 1 k : ℕ) : ℝ)
          ≤ ((⌈ε⌉₊ : ℕ) : ℝ) := le_trans hk1 (Nat.le_ceil ε)
      exact_mod_cast h
    have hc2 : wordDist S.enlarged.alphabet.carrier 1 (z⁻¹ * k * z) ≤ ⌈ε⌉₊ := by
      have h : ((wordDist S.enlarged.alphabet.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ)
          ≤ ((⌈ε⌉₊ : ℕ) : ℝ) := le_trans hk2 (Nat.le_ceil ε)
      exact_mod_cast h
    refine ⟨?_, ?_⟩
    · have h := S.sep_le_dist 1 k
      omega
    · have h := S.sep_le_dist 1 (z⁻¹ * k * z)
      have hmove : S.sep (z * 1) (z * (z⁻¹ * k * z)) = S.sep 1 (z⁻¹ * k * z) :=
        S.sep_smul z 1 (z⁻¹ * k * z)
      have he : z * (z⁻¹ * k * z) = k * z := by group
      rw [mul_one, he] at hmove
      omega
  exact ⟨hfin.subset hsub, le_trans (Set.ncard_le_ncard hsub hfin) hcard⟩

end SepData

/-- **The remaining input of Theorem 5.4**, in the shape §4–§5 delivers it:
the separating-coset data exists and its counting function has the
Lemma 5.11 bound. -/
def SepDataStatement : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    ∃ S : SepData D, S.AcylindricalCore

/-- **`OsinEnlargementBasepoint` from the separating-coset data.**  With
`osinTheorem54_of_basepoint` this reduces Osin's Theorem 5.4 to
`SepDataStatement`. -/
theorem osinEnlargementBasepoint_of (h : SepDataStatement.{u}) :
    OsinEnlargementBasepoint.{u} := by
  intro G _inst D hD
  obtain ⟨S, hcore⟩ := h G D hD
  refine ⟨S.enlarged, S.base_subset, S.fam_eq, S.emb, ?_⟩
  have hacy := S.isAcylindrical_of_core hcore
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hacy ε hε
  refine ⟨R, N, ?_⟩
  intro z hzd
  have hdist : R ≤ dist (Cayley.base S.enlarged.alphabet)
      (Cayley.of S.enlarged.alphabet z) := by
    rw [dist_val]
    simpa using hzd
  obtain ⟨hfin, hcard⟩ := hRN (Cayley.base S.enlarged.alphabet)
    (Cayley.of S.enlarged.alphabet z) hdist
  have hset : {k : G |
      dist (Cayley.base S.enlarged.alphabet)
          (k • Cayley.base S.enlarged.alphabet) ≤ ε ∧
        dist (Cayley.of S.enlarged.alphabet z)
          (k • Cayley.of S.enlarged.alphabet z) ≤ ε}
      = {k : G |
        ((wordDist S.enlarged.alphabet.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
          ((wordDist S.enlarged.alphabet.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ)
            ≤ ε} := by
    ext k
    simp only [Set.mem_setOf_eq, dist_smul_val, Cayley.val_base, Cayley.val_of,
      inv_one, one_mul, mul_one]
  rw [hset] at hfin hcard
  exact ⟨hfin, hcard⟩

/-- **Theorem 5.4 from the separating-coset data.** -/
theorem osinTheorem54_of_sepData (h : SepDataStatement.{u}) :
    OsinTheorem54.{u} :=
  osinTheorem54_of_basepoint (osinEnlargementBasepoint_of h)

end OsinEnlargement
end GGT
end GroupApproximation
