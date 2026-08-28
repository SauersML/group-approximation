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
`SepData.isAcylindrical_of_core` proves clause (b) from them together with one
residue, `SepData.AcylindricalCore`, and one further citation, `OsinLemma24`.
The obligation is:

> for each `m` there are `R > 0`, `N` such that for every `z` with
> `d_{Y⊔ℋ}(1,z) = R` exactly, at most `N` elements `k` have `d_{Y⊔ℋ}(1,k) ≤ m`
> and `d_{Y⊔ℋ}(1, z⁻¹kz) ≤ m`.

Two things about that shape are deliberate.  It is an *equation* `= R`, not
`≥ R`, because that is what Osin proves --- his (35) fixes `|g|_{Y⊔ℋ} = 18ε+11`
--- and Lemma 2.4 is what carries it back to acylindricity; an earlier version
of this file asked for `≥ R` and was therefore a strictly stronger statement
than the source establishes.  And it is stated in the enlarged word metric, not
in `sep`, because the *conclusion* of Lemma 5.11 is about `Γ(G, Y ⊔ ℋ)`; the
separating-coset count enters only inside its proof, which is where the linear
order of Lemma 4.8 and the local finiteness of `d̂_λ` do their work.

Two reductions are used to get there and they are different statements:
`GGT.OsinEnlargement.isAcylindrical_cayley_of_basepoint` and its exact-distance
twin `exactAcylindrical_of_basepoint` remove the quantifier over the first
vertex and need no hyperbolicity --- Osin takes that step silently ---
while `OsinLemma24` replaces `d(x,z) = R` by `R ≤ d(x,z)` and does need it.

Nothing in this module inhabits `SepData` or `AcylindricalCore`.  The component
machinery the separating cosets are built from is
`GGT/OsinComponents.lean` and `GGT/OsinPenetration.lean`; `sep` itself is
`OsinComponents.sepCard`, available once `LemmaFourEight` is proved.
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

/-- **Osin, *Acylindrically hyperbolic groups*, Lemma 2.4**, verbatim:

> The action of a group `G` on a hyperbolic space `S` is acylindrical if and
> only if for every `ε > 0` there exist `R, N > 0` such that for every two
> points `x, z` satisfying `d(x,z) = R`, we have
> `♯{g ∈ G | max{d(x,gx), d(z,gz)} ≤ ε} ≤ N`.

Only the direction that is used is carried: the exact-distance condition
implies acylindricity.  That direction is not free --- passing from pairs at
distance exactly `R` to all pairs at distance at least `R` needs the space to be
hyperbolic, through the Rips condition --- which is why `δ` and the four-point
hypothesis appear, and why this is a citation rather than bookkeeping.

It is a *different* reduction from `isAcylindrical_cayley_of_basepoint`, which
needs no hyperbolicity: that one removes the quantifier over the first vertex,
this one replaces `R ≤ d(x,z)` by `d(x,z) = R`.  Both are used, and Osin states
only this one; the basepoint step he takes silently inside Lemma 5.11.

(The source prints `d(y,gz)` where `d(z,gz)` is meant; no `y` occurs.) -/
def OsinLemma24 : Prop :=
  ∀ (Γ : Type u) [Group Γ] (X : Type u) [PseudoMetricSpace X] [MulAction Γ X]
    (δ : ℝ), IsHyperbolicSpace δ X → IsIsometricAction Γ X →
    (∀ ε : ℝ, 0 < ε → ∃ (R : ℝ) (N : ℕ), 0 < R ∧ ∀ x z : X, dist x z = R →
      {g : Γ | dist x (g • x) ≤ ε ∧ dist z (g • z) ≤ ε}.Finite ∧
        {g : Γ | dist x (g • x) ≤ ε ∧ dist z (g • z) ≤ ε}.ncard ≤ N) →
    IsAcylindrical Γ X

/-- The basepoint reduction in the exact-distance form Lemma 2.4 consumes.  The
argument is the one of `isAcylindrical_cayley_of_basepoint`: the `ε`-stabiliser
of `(x,z)` is carried by `k ↦ x k x⁻¹` from the `ε`-stabiliser of `(1, x⁻¹z)`,
and `d(x,z) = d(1, x⁻¹z)`.  Here it is an inclusion rather than an equality,
because the real bound `ε` is relaxed to the integer `⌈ε⌉₊`, which is all the
count needs. -/
theorem exactAcylindrical_of_basepoint (A : Alphabet G) (ε : ℝ) (R₀ N : ℕ)
    (h : ∀ z : G, wordDist A.carrier 1 z = R₀ →
      {k : G | wordDist A.carrier 1 k ≤ ⌈ε⌉₊ ∧
          wordDist A.carrier 1 (z⁻¹ * k * z) ≤ ⌈ε⌉₊}.Finite ∧
        {k : G | wordDist A.carrier 1 k ≤ ⌈ε⌉₊ ∧
          wordDist A.carrier 1 (z⁻¹ * k * z) ≤ ⌈ε⌉₊}.ncard ≤ N) :
    ∀ x z : Cayley A, dist x z = ((R₀ : ℕ) : ℝ) →
      {g : G | dist x (g • x) ≤ ε ∧ dist z (g • z) ≤ ε}.Finite ∧
        {g : G | dist x (g • x) ≤ ε ∧ dist z (g • z) ≤ ε}.ncard ≤ N := by
  intro x z hxz
  have hzd : wordDist A.carrier 1 ((Cayley.val x)⁻¹ * Cayley.val z) = R₀ := by
    have h1 : ((wordDist A.carrier 1
        ((Cayley.val x)⁻¹ * Cayley.val z) : ℕ) : ℝ) = ((R₀ : ℕ) : ℝ) := by
      rw [← dist_val]
      exact hxz
    exact_mod_cast h1
  obtain ⟨hfin, hcard⟩ := h _ hzd
  have hsub : {g : G | dist x (g • x) ≤ ε ∧ dist z (g • z) ≤ ε}
      ⊆ (fun k : G => Cayley.val x * k * (Cayley.val x)⁻¹) ''
        {k : G | wordDist A.carrier 1 k ≤ ⌈ε⌉₊ ∧
          wordDist A.carrier 1
            (((Cayley.val x)⁻¹ * Cayley.val z)⁻¹ * k *
              ((Cayley.val x)⁻¹ * Cayley.val z)) ≤ ⌈ε⌉₊} := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨(Cayley.val x)⁻¹ * g * Cayley.val x, ⟨?_, ?_⟩, by group⟩
    · have h1 : ((wordDist A.carrier 1
          ((Cayley.val x)⁻¹ * g * Cayley.val x) : ℕ) : ℝ)
          ≤ ((⌈ε⌉₊ : ℕ) : ℝ) := by
        rw [← dist_smul_val]
        exact le_trans hg1 (Nat.le_ceil ε)
      exact_mod_cast h1
    · have hconj : ((Cayley.val x)⁻¹ * Cayley.val z)⁻¹ *
            ((Cayley.val x)⁻¹ * g * Cayley.val x) *
            ((Cayley.val x)⁻¹ * Cayley.val z)
          = (Cayley.val z)⁻¹ * g * Cayley.val z := by group
      rw [hconj]
      have h2 : ((wordDist A.carrier 1
          ((Cayley.val z)⁻¹ * g * Cayley.val z) : ℕ) : ℝ)
          ≤ ((⌈ε⌉₊ : ℕ) : ℝ) := by
        rw [← dist_smul_val]
        exact le_trans hg2 (Nat.le_ceil ε)
      exact_mod_cast h2
  refine ⟨(hfin.image _).subset hsub, ?_⟩
  exact le_trans (Set.ncard_le_ncard hsub (hfin.image _))
    (le_trans (Set.ncard_image_le hfin) hcard)

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

/-- **Osin's Lemma 5.11, with the geometry removed**, in the exact-distance
form his proof actually establishes: he fixes `|g|_{Y⊔ℋ} = 18ε + 11`, an
equation, because Lemma 2.4 lets him check only pairs at one distance.

An earlier version of this statement asked for the bound at every `z` with
`sep 1 z ≥ R`.  That is strictly stronger than what Osin proves, so it was the
wrong target; the exact-distance form is the right one, and `OsinLemma24` is
what carries it back to acylindricity.  Stated in the enlarged word metric
rather than in `sep`, because the conclusion of Lemma 5.11 is about
`Γ(G, Y ⊔ ℋ)`; the separating-coset count enters only inside its proof. -/
def AcylindricalCore : Prop :=
  ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
    wordDist S.enlarged.alphabet.carrier 1 z = R →
      {k : G | wordDist S.enlarged.alphabet.carrier 1 k ≤ m ∧
          wordDist S.enlarged.alphabet.carrier 1 (z⁻¹ * k * z) ≤ m}.Finite ∧
        {k : G | wordDist S.enlarged.alphabet.carrier 1 k ≤ m ∧
          wordDist S.enlarged.alphabet.carrier 1
            (z⁻¹ * k * z) ≤ m}.ncard ≤ N

/-- **Clause (b) of Theorem 5.4 from the residue.**

`exactAcylindrical_of_basepoint` removes the quantifier over the first vertex
--- the step Osin takes silently --- and `OsinLemma24` passes from pairs at one
distance to all distant pairs, which is where hyperbolicity is used.  The
hyperbolicity constant is the one `IsHyperbolicallyEmbedded` already carries,
so no new input is needed for it. -/
theorem isAcylindrical_of_core (h24 : OsinLemma24.{u})
    (hcore : S.AcylindricalCore) :
    IsAcylindrical G (Cayley S.enlarged.alphabet) := by
  obtain ⟨δ, hδ⟩ := S.emb.hyperbolic
  refine h24 G (Cayley S.enlarged.alphabet) δ hδ
    (isIsometricAction_cayley S.enlarged.alphabet) ?_
  intro ε hε
  obtain ⟨R, N, hRpos, hRN⟩ := hcore ⌈ε⌉₊
  refine ⟨((R : ℕ) : ℝ), N, ?_, ?_⟩
  · exact_mod_cast hRpos
  · exact exactAcylindrical_of_basepoint S.enlarged.alphabet ε R N hRN

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
theorem osinEnlargementBasepoint_of (h24 : OsinLemma24.{u})
    (h : SepDataStatement.{u}) : OsinEnlargementBasepoint.{u} := by
  intro G _inst D hD
  obtain ⟨S, hcore⟩ := h G D hD
  refine ⟨S.enlarged, S.base_subset, S.fam_eq, S.emb, ?_⟩
  have hacy := S.isAcylindrical_of_core h24 hcore
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
theorem osinTheorem54_of_sepData (h24 : OsinLemma24.{u})
    (h : SepDataStatement.{u}) : OsinTheorem54.{u} :=
  osinTheorem54_of_basepoint (osinEnlargementBasepoint_of h24 h)

end OsinEnlargement
end GGT
end GroupApproximation
