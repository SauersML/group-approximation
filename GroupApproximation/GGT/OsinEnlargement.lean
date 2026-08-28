import GroupApproximation.GGT.WPDAcylindricalHyperbolicity

/-!
# Osin's Theorem 5.4: shrinking the leaf

`GGT/WPDAcylindricalHyperbolicity.lean` reduces `(AH₄) ⇒ (AH₁)` to two named
literature propositions, of which `OsinTheorem54` is the geometric one:

> **Osin, *Acylindrically hyperbolic groups*, Theorem 5.4.**  Let `G` be a
> group, `{H_λ}` a finite collection of subgroups, `X ⊆ G`, and suppose
> `{H_λ} ↪_h (G,X)`.  Then there is `Y ⊇ X` with (a) `{H_λ} ↪_h (G,Y)` and
> (b) the action of `G` on `Γ(G, Y ⊔ H)` acylindrical.

That is several pages of §5 and this module does not prove it.  What it does is
make the leaf smaller and record why the obvious shortcuts are closed.

## The plan

1. **Neither clause is inherited.**  `alphabet_mono` and `relBall_mono` say that
   enlarging the base grows the alphabet and grows every relative ball.  So
   clause (a) is a genuine obligation on `Y`: hyperbolic embedding of `X` gives
   local finiteness of the `X`-relative balls, and the `Y`-relative balls are
   larger.  Nobody should expect (a) for free.
2. **The enlargement is necessary.**  `osinTheorem54_of_acylindrical` disposes
   of the case where `X` already works, so the content of Theorem 5.4 is
   exactly the case where it does not --- which, by Osin's own counterexample
   quoted at `OsinTheorem54`, is a case that occurs.
3. **One quantifier comes off the target.**
   `isAcylindrical_cayley_of_basepoint` --- proved here --- says that on a
   Cayley graph acylindricity only has to be checked at the identity vertex:
   the `ε`-stabiliser of a pair `(x,y)` is the conjugate by `x` of the
   `ε`-stabiliser of `(1, x⁻¹y)`, and conjugation is a bijection, so it
   preserves both finiteness and cardinality.  This is the form Osin's argument
   produces its bound in, and it turns the target from a statement about pairs
   of vertices into one about single group elements and word lengths.
4. `OsinEnlargementBasepoint` is `OsinTheorem54` with clause (b) in that
   reduced form, and `osinTheorem54_of_basepoint` closes the gap between them.

## The remaining leaf

`OsinEnlargementBasepoint`.  Nothing here inhabits it, and its geometric
content is untouched: producing `Y`, and bounding, for every `ε`, the number of
`k ∈ G` with `|k|_{Y⊔H} ≤ ε` and `|z⁻¹kz|_{Y⊔H} ≤ ε` for every sufficiently
long `z`.  Osin obtains that bound from the isolated-component machinery of
Dahmani--Guirardel--Osin §4; no part of that machinery is formalized in this
repository, and this module does not pretend otherwise.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The word metric of a Cayley graph, at the identity -/

variable {G : Type u} [Group G]

/-- The distance between two vertices of `Γ(G,A)` is the word length of the
quotient of their names. -/
theorem dist_val (A : Alphabet G) (x y : Cayley A) :
    dist x y
      = ((wordDist A.carrier 1 ((Cayley.val x)⁻¹ * Cayley.val y) : ℕ) : ℝ) := by
  have h1 := wordDist_left_invariant A.carrier (Cayley.val x)⁻¹
    (Cayley.val x) (Cayley.val y)
  rw [inv_mul_cancel] at h1
  simp only [Cayley.dist_eq]
  rw [← h1]

/-- The displacement of a vertex is the word length of a conjugate. -/
theorem dist_smul_val (A : Alphabet G) (x : Cayley A) (k : G) :
    dist x (k • x)
      = ((wordDist A.carrier 1
          ((Cayley.val x)⁻¹ * k * Cayley.val x) : ℕ) : ℝ) := by
  have h1 := wordDist_left_invariant A.carrier (Cayley.val x)⁻¹
    (Cayley.val x) (k * Cayley.val x)
  rw [inv_mul_cancel] at h1
  have h3 : (Cayley.val x)⁻¹ * (k * Cayley.val x)
      = (Cayley.val x)⁻¹ * k * Cayley.val x := by group
  rw [h3] at h1
  simp only [Cayley.dist_eq, Cayley.val_smul]
  rw [← h1]

/-! ## Acylindricity of a Cayley graph is a basepoint condition -/

/-- **On a Cayley graph, acylindricity only has to be checked at the identity
vertex.**

The `ε`-stabiliser of a pair `(x,y)` is the image under `k ↦ x k x⁻¹` of the
`ε`-stabiliser of `(1, x⁻¹y)`, because the translation action is transitive and
by isometries.  Conjugation is a bijection, so it carries finiteness and
cardinality across, and the quantifier over the first vertex disappears. -/
theorem isAcylindrical_cayley_of_basepoint (A : Alphabet G)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (R : ℝ) (N : ℕ), ∀ z : G,
      R ≤ ((wordDist A.carrier 1 z : ℕ) : ℝ) →
        {k : G | ((wordDist A.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
            ((wordDist A.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ) ≤ ε}.Finite ∧
          {k : G | ((wordDist A.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
            ((wordDist A.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ) ≤ ε}.ncard ≤ N) :
    IsAcylindrical G (Cayley A) := by
  intro ε hε
  obtain ⟨R, N, hRN⟩ := h ε hε
  refine ⟨R, N, ?_⟩
  intro x y hxy
  have hzdist : R ≤ ((wordDist A.carrier 1
      ((Cayley.val x)⁻¹ * Cayley.val y) : ℕ) : ℝ) := by
    rw [← dist_val]
    exact hxy
  obtain ⟨hfin, hcard⟩ := hRN ((Cayley.val x)⁻¹ * Cayley.val y) hzdist
  have hconj : ∀ g : G,
      ((Cayley.val x)⁻¹ * Cayley.val y)⁻¹ *
          ((Cayley.val x)⁻¹ * g * Cayley.val x) *
          ((Cayley.val x)⁻¹ * Cayley.val y)
        = (Cayley.val y)⁻¹ * g * Cayley.val y := by
    intro g
    group
  have hset : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}
      = (fun k : G => Cayley.val x * k * (Cayley.val x)⁻¹) ''
        {k : G | ((wordDist A.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
          ((wordDist A.carrier 1
            (((Cayley.val x)⁻¹ * Cayley.val y)⁻¹ * k *
              ((Cayley.val x)⁻¹ * Cayley.val y)) : ℕ) : ℝ) ≤ ε} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image, dist_smul_val]
    constructor
    · intro hg
      refine ⟨(Cayley.val x)⁻¹ * g * Cayley.val x, ⟨hg.1, ?_⟩, by group⟩
      rw [hconj g]
      exact hg.2
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      have he1 : (Cayley.val x)⁻¹ * (Cayley.val x * k * (Cayley.val x)⁻¹) *
          Cayley.val x = k := by group
      have he2 : (Cayley.val y)⁻¹ *
            (Cayley.val x * k * (Cayley.val x)⁻¹) * Cayley.val y
          = ((Cayley.val x)⁻¹ * Cayley.val y)⁻¹ * k *
            ((Cayley.val x)⁻¹ * Cayley.val y) := by
        group
      rw [he1, he2]
      exact ⟨hk1, hk2⟩
  have hinj : Function.Injective
      (fun k : G => Cayley.val x * k * (Cayley.val x)⁻¹) := by
    intro p q hpq
    have h1 : Cayley.val x * p * (Cayley.val x)⁻¹
        = Cayley.val x * q * (Cayley.val x)⁻¹ := hpq
    have h2 := congrArg
      (fun z => (Cayley.val x)⁻¹ * z * Cayley.val x) h1
    simpa [mul_assoc] using h2
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  rw [Set.ncard_image_of_injective _ hinj]
  exact hcard

/-! ## Neither clause of Theorem 5.4 is inherited -/

variable {Λ : Type w}

/-- Enlarging the base enlarges the alphabet. -/
theorem alphabet_mono {D D' : RelGenSet G Λ} (hbase : D.base ⊆ D'.base)
    (hfam : D'.fam = D.fam) :
    D.alphabet.carrier ⊆ D'.alphabet.carrier := by
  rintro z (hz | hz)
  · exact Or.inl (hbase hz)
  · refine Or.inr ?_
    rw [hfam]
    exact hz

/-- Enlarging the base enlarges every relative ball, so local finiteness of the
`Y`-relative metrics does **not** follow from local finiteness of the
`X`-relative ones.  This is why clause (a) of Theorem 5.4 is an obligation. -/
theorem relBall_mono {D D' : RelGenSet G Λ} (hbase : D.base ⊆ D'.base)
    (hfam : D'.fam = D.fam) (lam : Λ) (n : ℕ) :
    D.relBall lam n ⊆ D'.relBall lam n := by
  rintro z ⟨hz, wrd, hletters, hval, havoid, hlen⟩
  refine ⟨?_, wrd, ?_, hval, ?_, hlen⟩
  · rw [hfam]
    exact hz
  · intro a ha
    have h := hletters a ha
    cases a with
    | base t => exact hbase h
    | comp l t =>
        show t ∈ D'.fam l
        rw [hfam]
        exact h
  · rw [hfam]
    exact havoid

/-! ## The reduced leaf -/

/-- **Osin's Theorem 5.4 with clause (b) at the basepoint.**  Identical to
`OsinTheorem54` except that acylindricity of `Γ(G, Y ⊔ H)` is asked for in the
single-vertex form `isAcylindrical_cayley_of_basepoint` consumes: for every `ε`
a radius `R` and a bound `N` such that for every `z` of relative length at least
`R`, at most `N` elements `k` have both `k` and `z⁻¹kz` of relative length at
most `ε`.

This is the whole remaining geometric obligation of `(AH₄) ⇒ (AH₁)`.  Osin
derives the bound from the isolated-component machinery of
Dahmani--Guirardel--Osin §4, none of which is formalized here. -/
def OsinEnlargementBasepoint : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    ∃ D' : RelGenSet G Unit, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      D'.IsHyperbolicallyEmbedded ∧
      ∀ ε : ℝ, 0 < ε → ∃ (R : ℝ) (N : ℕ), ∀ z : G,
        R ≤ ((wordDist D'.alphabet.carrier 1 z : ℕ) : ℝ) →
          {k : G | ((wordDist D'.alphabet.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
              ((wordDist D'.alphabet.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ)
                ≤ ε}.Finite ∧
            {k : G | ((wordDist D'.alphabet.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
              ((wordDist D'.alphabet.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ)
                ≤ ε}.ncard ≤ N

/-- **The reduced leaf implies Theorem 5.4.** -/
theorem osinTheorem54_of_basepoint (h : OsinEnlargementBasepoint) :
    OsinTheorem54.{u} := by
  intro G _inst D hD
  obtain ⟨D', hbase, hfam, hemb, hacy⟩ := h G D hD
  exact ⟨D', hbase, hfam, hemb,
    isAcylindrical_cayley_of_basepoint D'.alphabet hacy⟩

/-- The case Theorem 5.4 does **not** have to cover: if the given relative
generating set already gives an acylindrical action, it is its own
enlargement. -/
theorem osinTheorem54_of_acylindrical
    (D : RelGenSet G Unit) (hD : D.IsHyperbolicallyEmbedded)
    (hacy : IsAcylindrical G (Cayley D.alphabet)) :
    ∃ D' : RelGenSet G Unit, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      D'.IsHyperbolicallyEmbedded ∧ IsAcylindrical G (Cayley D'.alphabet) :=
  ⟨D, subset_rfl, rfl, hD, hacy⟩

end OsinEnlargement
end GGT
end GroupApproximation
