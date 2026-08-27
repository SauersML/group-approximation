import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic
import GroupApproximation.Algebra.HyperbolicFreeGroup

/-!
# The first acylindrically hyperbolic group: a free group of finite rank

`Manuscript/NonMF/AcylindricallyHyperbolic.lean` defines
`IsAcylindricallyHyperbolic G` --- some generating set makes `Γ(G,A)`
hyperbolic, the translation action acylindrical, and `G` non-elementary --- and
until now the class had **no instance at all**: every consumer of Hull's
Theorem 3.12 in the repository ran on a hypothesis that nothing was known to
satisfy.  This module supplies the first witness, a free group of finite rank
at least two, and with it the three clauses separately, each proved for a
general Cayley graph rather than for the free group alone.

## The three clauses

**Hyperbolicity, at `δ = 0`.**  `Algebra/HyperbolicFreeGroup.lean` already
proves `Hyperbolic.IsTreeLike (freeAlphabet α) (fun x y => lcp x.toWord
y.toWord)`: the common-prefix length of reduced words satisfies the
cancellation identity `d(x,y) + 2 p(x,y) = |x| + |y|` and the ultrametric
inequality.  `gromovProduct_cayley_eq` reads off that the Gromov product of
`Γ(G,A)` based at `w` *is* `p(w⁻¹x, w⁻¹y)`, by left invariance of the word
metric, so Gromov's four-point condition at `δ = 0` is the ultrametric field
verbatim (`isHyperbolicSpace_zero_cayley`).

**Acylindricity, from a finite alphabet.**  A finite alphabet makes the balls
of the word metric finite (`wordNorm_ball_finite`, by induction on the radius:
the ball of radius `n+1` lies in `{1} ∪ S · B(n)`).  The set of elements moving
a vertex `x` of `Γ(G,A)` by at most `ε` is then the *conjugate* `x B(⌈ε⌉) x⁻¹`
of a ball, so it is finite with a cardinality bound independent of `x`.  Osin's
condition follows with `R = 0`: no separation between the two basepoints is
needed, because a proper action is acylindrical for the cheapest possible
reason (`isAcylindrical_cayley_of_finite`).

**Non-elementarity, from exponent sums.**  This is the only free-group-specific
input, and it is proved without touching reduced words.  For `f : α → ℤ` the
exponent-sum `expVal f` is a homomorphism to `ℤ`, and if two such functions
satisfy `|f₁ x| + |f₂ x| ≤ 1` pointwise --- as the indicators of two distinct
basis letters `a ≠ b` do --- then

```
    |expVal f₁ g| + |expVal f₂ g| ≤ |g|_A            (natAbs_add_natAbs_expVal_le)
```

because each letter contributes at most one to the left-hand side.  Applied to
`g = a⁻ⁿbᵐ` this reads `|n| + |m| ≤ |a⁻ⁿbᵐ|`, while subadditivity gives
`|aⁿ| ≤ |n|` and `|bᵐ| ≤ |m|`; so the Gromov product `(aⁿ · bᵐ)_1` is `≤ 0`,
which is independence, and `|aⁿ| ≥ n`, which is loxodromy at translation rate
one.

The `ℓ¹` shape of the hypothesis is what does the work: a single exponent sum
would only give `max (|n|, |m|) ≤ |a⁻ⁿbᵐ|`, which is too weak to force the
Gromov product down to zero.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Hyperbolic
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Balls of a finite alphabet are finite -/

section Ball

variable {G : Type u} [Group G]

/-- **Balls of the word metric of a finite alphabet are finite.**  The ball of
radius `n + 1` is contained in `S · B(n)` together with the identity, because a
shortest word for an element of that ball is either empty or begins with a
letter. -/
theorem wordNorm_ball_finite {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (hfin : S.Finite) (n : ℕ) : {g : G | wordNorm S g ≤ n}.Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton (1 : G)) ?_
    intro g hg
    have hg0 : wordNorm S g = 0 := Nat.le_zero.mp hg
    exact (wordNorm_eq_zero_iff hS g).mp hg0
  | succ n ih =>
    refine Set.Finite.subset
      (Set.Finite.union (Set.Finite.image2 (fun a b : G => a * b) hfin ih)
        (Set.finite_singleton (1 : G))) ?_
    intro g hg
    have hgn : wordNorm S g ≤ n + 1 := hg
    obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
    cases l with
    | nil =>
      have hg1 : g = 1 := by rw [← hl.prod_eq, List.prod_nil]
      exact Or.inr hg1
    | cons s t =>
      have hgeq : g = s * t.prod := by rw [← hl.prod_eq, List.prod_cons]
      have hsS : s ∈ S := hl.letters s (List.mem_cons_self s t)
      have htw : IsWord S t t.prod :=
        ⟨fun x hx => hl.letters x (List.mem_cons_of_mem s hx), rfl⟩
      have htn : wordNorm S t.prod ≤ n := by
        have h1 := wordNorm_le_length htw
        rw [List.length_cons] at hlen
        omega
      rw [hgeq]
      exact Or.inl (Set.mem_image2_of_mem hsS htn)

end Ball

/-! ## Acylindricity of a Cayley graph with a finite alphabet -/

/-- **A proper translation action is acylindrical.**  With a finite alphabet the
`ε`-almost-stabiliser of a vertex `x` of `Γ(G,A)` is the conjugate by `x` of the
ball of radius `⌈ε⌉`, so it is finite with a bound independent of `x`; the
second basepoint is never used, and `R = 0` works. -/
theorem isAcylindrical_cayley_of_finite {G : Type u} [Group G] (A : Alphabet G)
    (hfin : A.carrier.Finite) : IsAcylindrical G (Cayley A) := by
  intro ε _hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ε ≤ (n : ℝ) := ⟨⌈ε⌉₊, Nat.le_ceil ε⟩
  refine ⟨0, {g : G | wordNorm A.carrier g ≤ n}.ncard, ?_⟩
  intro x y _
  have hball : {g : G | wordNorm A.carrier g ≤ n}.Finite :=
    wordNorm_ball_finite A.symmetricGenerating hfin n
  have hinj : Function.Injective
      (fun g : G => Cayley.val x * g * (Cayley.val x)⁻¹) := by
    intro p q hpq
    have hpq' : Cayley.val x * p * (Cayley.val x)⁻¹
        = Cayley.val x * q * (Cayley.val x)⁻¹ := hpq
    exact mul_left_cancel (mul_right_cancel hpq')
  have hsub : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε} ⊆
      (fun g : G => Cayley.val x * g * (Cayley.val x)⁻¹) ''
        {g : G | wordNorm A.carrier g ≤ n} := by
    rintro g ⟨h1, -⟩
    have hd : dist x (g • x)
        = ((wordNorm A.carrier ((Cayley.val x)⁻¹ * (g * Cayley.val x)) : ℕ) : ℝ) := by
      rw [Cayley.dist_eq, Cayley.val_smul]
      rfl
    rw [hd] at h1
    refine ⟨(Cayley.val x)⁻¹ * (g * Cayley.val x), ?_, ?_⟩
    · have h2 : ((wordNorm A.carrier
          ((Cayley.val x)⁻¹ * (g * Cayley.val x)) : ℕ) : ℝ) ≤ (n : ℝ) :=
        le_trans h1 hn
      exact_mod_cast h2
    · show Cayley.val x * ((Cayley.val x)⁻¹ * (g * Cayley.val x))
          * (Cayley.val x)⁻¹ = g
      group
  refine ⟨Set.Finite.subset (hball.image _) hsub, ?_⟩
  calc {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.ncard
      ≤ ((fun g : G => Cayley.val x * g * (Cayley.val x)⁻¹) ''
          {g : G | wordNorm A.carrier g ≤ n}).ncard :=
        Set.ncard_le_ncard hsub (hball.image _)
    _ = {g : G | wordNorm A.carrier g ≤ n}.ncard :=
        Set.ncard_image_of_injective _ hinj

/-! ## A tree-like alphabet makes the Cayley graph `0`-hyperbolic -/

/-- **The Gromov product of `Γ(G,A)` is the common-prefix length.**  Left
invariance of the word metric moves the basepoint to the identity, and the
cancellation identity of `IsTreeLike` then evaluates the product exactly. -/
theorem gromovProduct_cayley_eq {G : Type u} [Group G] {A : Alphabet G}
    {p : G → G → ℕ} (h : IsTreeLike A.carrier p) (x y w : Cayley A) :
    gromovProduct x y w
      = (p ((Cayley.val w)⁻¹ * Cayley.val x)
          ((Cayley.val w)⁻¹ * Cayley.val y) : ℝ) := by
  have hS := A.symmetricGenerating
  have hsplit := h.split ((Cayley.val w)⁻¹ * Cayley.val x)
    ((Cayley.val w)⁻¹ * Cayley.val y)
  have hinv : wordDist A.carrier ((Cayley.val w)⁻¹ * Cayley.val x)
      ((Cayley.val w)⁻¹ * Cayley.val y)
      = wordDist A.carrier (Cayley.val x) (Cayley.val y) :=
    wordDist_left_invariant A.carrier (Cayley.val w)⁻¹ (Cayley.val x)
      (Cayley.val y)
  have hnx : wordNorm A.carrier ((Cayley.val w)⁻¹ * Cayley.val x)
      = wordDist A.carrier (Cayley.val w) (Cayley.val x) := rfl
  have hny : wordNorm A.carrier ((Cayley.val w)⁻¹ * Cayley.val y)
      = wordDist A.carrier (Cayley.val w) (Cayley.val y) := rfl
  rw [hinv, hnx, hny] at hsplit
  have hreal : ((wordDist A.carrier (Cayley.val x) (Cayley.val y) : ℕ) : ℝ)
      + 2 * (p ((Cayley.val w)⁻¹ * Cayley.val x)
          ((Cayley.val w)⁻¹ * Cayley.val y) : ℝ)
      = ((wordDist A.carrier (Cayley.val w) (Cayley.val x) : ℕ) : ℝ)
        + ((wordDist A.carrier (Cayley.val w) (Cayley.val y) : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  have hcx : wordDist A.carrier (Cayley.val x) (Cayley.val w)
      = wordDist A.carrier (Cayley.val w) (Cayley.val x) :=
    wordDist_comm hS _ _
  have hcy : wordDist A.carrier (Cayley.val y) (Cayley.val w)
      = wordDist A.carrier (Cayley.val w) (Cayley.val y) :=
    wordDist_comm hS _ _
  simp only [gromovProduct, Cayley.dist_eq]
  rw [hcx, hcy]
  linarith

/-- **A tree-like alphabet makes `Γ(G,A)` `0`-hyperbolic.**  After
`gromovProduct_cayley_eq` the four-point condition *is* the ultrametric
inequality, so no constant is lost. -/
theorem isHyperbolicSpace_zero_cayley {G : Type u} [Group G] {A : Alphabet G}
    {p : G → G → ℕ} (h : IsTreeLike A.carrier p) :
    IsHyperbolicSpace 0 (Cayley A) := by
  intro w x y z
  rw [gromovProduct_comm y z w, gromovProduct_cayley_eq h x y w,
    gromovProduct_cayley_eq h z y w, gromovProduct_cayley_eq h x z w]
  have key := h.ultra ((Cayley.val w)⁻¹ * Cayley.val x)
    ((Cayley.val w)⁻¹ * Cayley.val z) ((Cayley.val w)⁻¹ * Cayley.val y)
  have key' : min ((p ((Cayley.val w)⁻¹ * Cayley.val x)
        ((Cayley.val w)⁻¹ * Cayley.val y) : ℕ) : ℝ)
      ((p ((Cayley.val w)⁻¹ * Cayley.val z)
        ((Cayley.val w)⁻¹ * Cayley.val y) : ℕ) : ℝ)
      ≤ ((p ((Cayley.val w)⁻¹ * Cayley.val x)
        ((Cayley.val w)⁻¹ * Cayley.val z) : ℕ) : ℝ) := by
    exact_mod_cast key
  linarith

/-! ## Distances in a Cayley graph at the basepoint -/

section Base

variable {G : Type u} [Group G] (A : Alphabet G)

/-- The displacement of the basepoint is the word length. -/
theorem dist_base_smul (g : G) :
    dist (Cayley.base A) (g • Cayley.base A) = (wordNorm A.carrier g : ℝ) := by
  simp only [Cayley.dist_eq, Cayley.val_smul, Cayley.val_base, mul_one]
  exact_mod_cast wordDist_one_left A.carrier g

/-- The distance between two orbit points of the basepoint. -/
theorem dist_smul_base_smul (g h : G) :
    dist (g • Cayley.base A) (h • Cayley.base A)
      = (wordNorm A.carrier (g⁻¹ * h) : ℝ) := by
  simp only [Cayley.dist_eq, Cayley.val_smul, Cayley.val_base, mul_one]
  rfl

end Base

/-! ## Powers do not outgrow their exponent -/

section Powers

variable {G : Type u} [Group G]

/-- Subadditivity, iterated: a power of a letter has word length at most the
exponent. -/
theorem wordNorm_pow_le {S : Set G} (hS : IsSymmetricGeneratingSet S) {g : G}
    (hg : g ∈ S) (k : ℕ) : wordNorm S (g ^ k) ≤ k := by
  induction k with
  | zero =>
    have h0 : wordNorm S (g ^ 0) = 0 := by rw [pow_zero, wordNorm_one]
    omega
  | succ k ih =>
    rw [pow_succ]
    have h1 := wordNorm_mul_le hS (g ^ k) g
    have h2 := wordNorm_le_one_of_mem hg
    omega

/-- The same over the integers: inverting a word does not change its length. -/
theorem wordNorm_zpow_le {S : Set G} (hS : IsSymmetricGeneratingSet S) {g : G}
    (hg : g ∈ S) (n : ℤ) : wordNorm S (g ^ n) ≤ n.natAbs := by
  have hnat : ∀ k : ℕ, wordNorm S (g ^ (k : ℤ)) ≤ k := by
    intro k
    rw [zpow_natCast]
    exact wordNorm_pow_le hS hg k
  rcases Int.natAbs_eq n with hcase | hcase
  · calc wordNorm S (g ^ n)
        = wordNorm S (g ^ ((n.natAbs : ℤ))) := by rw [← hcase]
      _ ≤ n.natAbs := hnat n.natAbs
  · calc wordNorm S (g ^ n)
        = wordNorm S (g ^ (-(n.natAbs : ℤ))) := by rw [← hcase]
      _ = wordNorm S ((g ^ ((n.natAbs : ℤ)))⁻¹) := by rw [zpow_neg]
      _ = wordNorm S (g ^ ((n.natAbs : ℤ))) := wordNorm_inv hS _
      _ ≤ n.natAbs := hnat n.natAbs

end Powers

/-! ## Exponent sums in a free group -/

section ExpVal

variable {α : Type} [DecidableEq α]

/-- The exponent-sum homomorphism attached to a weighting `f` of the basis. -/
noncomputable def expHom (f : α → ℤ) : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift fun x => Multiplicative.ofAdd (f x)

/-- The exponent sum of `g`, weighted by `f`. -/
noncomputable def expVal (f : α → ℤ) (g : FreeGroup α) : ℤ :=
  Multiplicative.toAdd (expHom f g)

theorem expVal_one (f : α → ℤ) : expVal f 1 = 0 :=
  congrArg Multiplicative.toAdd (map_one (expHom f))

theorem expVal_mul (f : α → ℤ) (u v : FreeGroup α) :
    expVal f (u * v) = expVal f u + expVal f v :=
  congrArg Multiplicative.toAdd (map_mul (expHom f) u v)

theorem expVal_inv (f : α → ℤ) (u : FreeGroup α) :
    expVal f u⁻¹ = -expVal f u :=
  congrArg Multiplicative.toAdd (map_inv (expHom f) u)

theorem expVal_of (f : α → ℤ) (c : α) : expVal f (FreeGroup.of c) = f c := by
  show Multiplicative.toAdd (expHom f (FreeGroup.of c)) = f c
  unfold expHom
  rw [FreeGroup.lift_apply_of]
  rfl

theorem expVal_zpow (f : α → ℤ) (u : FreeGroup α) (n : ℤ) :
    expVal f (u ^ n) = n * expVal f u := by
  show Multiplicative.toAdd (expHom f (u ^ n))
    = n * Multiplicative.toAdd (expHom f u)
  rw [map_zpow]
  simp only [toAdd_zpow, zsmul_eq_mul, Int.cast_id]

/-- **One letter contributes at most one.**  For an `ℓ¹`-bounded pair of
weightings the two exponent sums of a single letter of the alphabet together
weigh at most one. -/
theorem natAbs_add_natAbs_expVal_letter {f₁ f₂ : α → ℤ}
    (hf : ∀ x : α, (f₁ x).natAbs + (f₂ x).natAbs ≤ 1) {z : FreeGroup α}
    (hz : z ∈ freeAlphabet α) :
    (expVal f₁ z).natAbs + (expVal f₂ z).natAbs ≤ 1 := by
  obtain ⟨⟨c, s⟩, rfl⟩ := hz
  cases s
  · have e1 : expVal f₁ (letterOf (c, false)) = -f₁ c := by
      show expVal f₁ (FreeGroup.of c)⁻¹ = -f₁ c
      rw [expVal_inv, expVal_of]
    have e2 : expVal f₂ (letterOf (c, false)) = -f₂ c := by
      show expVal f₂ (FreeGroup.of c)⁻¹ = -f₂ c
      rw [expVal_inv, expVal_of]
    have h := hf c
    rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg]
    exact h
  · have e1 : expVal f₁ (letterOf (c, true)) = f₁ c := expVal_of f₁ c
    have e2 : expVal f₂ (letterOf (c, true)) = f₂ c := expVal_of f₂ c
    have h := hf c
    rw [e1, e2]
    exact h

/-- The same bound along an arbitrary product of letters. -/
theorem natAbs_add_natAbs_expVal_prod_le {f₁ f₂ : α → ℤ}
    (hf : ∀ x : α, (f₁ x).natAbs + (f₂ x).natAbs ≤ 1) :
    ∀ l : List (FreeGroup α), (∀ z ∈ l, z ∈ freeAlphabet α) →
      (expVal f₁ l.prod).natAbs + (expVal f₂ l.prod).natAbs ≤ l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    rw [List.prod_nil, expVal_one, expVal_one]
    simp
  | cons z t ih =>
    intro hz
    have h1 : z ∈ freeAlphabet α := hz z (List.mem_cons_self z t)
    have h2 := ih fun w hw => hz w (List.mem_cons_of_mem z hw)
    have h3 := natAbs_add_natAbs_expVal_letter hf h1
    rw [List.prod_cons, expVal_mul, expVal_mul, List.length_cons]
    have b1 := Int.natAbs_add_le (expVal f₁ z) (expVal f₁ t.prod)
    have b2 := Int.natAbs_add_le (expVal f₂ z) (expVal f₂ t.prod)
    omega

/-- **The `ℓ¹` lower bound on word length.**  For a pointwise `ℓ¹`-bounded pair
of weightings the two exponent sums together are dominated by the word length
over the basis alphabet.  This is the only free-group input to non-elementarity,
and it never mentions reduced words. -/
theorem natAbs_add_natAbs_expVal_le {f₁ f₂ : α → ℤ}
    (hf : ∀ x : α, (f₁ x).natAbs + (f₂ x).natAbs ≤ 1) (g : FreeGroup α) :
    (expVal f₁ g).natAbs + (expVal f₂ g).natAbs
      ≤ wordNorm (freeAlphabet α) g := by
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq (isSymmetricGeneratingSet_freeAlphabet (α := α)) g
  have h := natAbs_add_natAbs_expVal_prod_le hf l hl.letters
  rw [hl.prod_eq, hlen] at h
  exact h

end ExpVal

/-! ## Two basis letters are independent loxodromics -/

section FreeGroupAH

variable {α : Type} [DecidableEq α]

/-- The indicator weighting of a basis letter. -/
def basisWeight (a : α) : α → ℤ := fun x => if x = a then 1 else 0

@[simp] theorem basisWeight_self (a : α) : basisWeight a a = 1 := by
  rw [basisWeight, if_pos rfl]

theorem basisWeight_of_ne {a c : α} (h : c ≠ a) : basisWeight a c = 0 := by
  rw [basisWeight, if_neg h]

/-- Two distinct basis letters give a pointwise `ℓ¹`-bounded pair of
weightings. -/
theorem natAbs_basisWeight_add_le {a b : α} (hab : a ≠ b) (x : α) :
    (basisWeight a x).natAbs + (basisWeight b x).natAbs ≤ 1 := by
  by_cases h1 : x = a
  · have h2 : x ≠ b := by
      rw [h1]
      exact hab
    rw [basisWeight, basisWeight, if_pos h1, if_neg h2]
  · rw [basisWeight, if_neg h1]
    by_cases h2 : x = b
    · rw [basisWeight, if_pos h2]
    · rw [basisWeight, if_neg h2]

/-- **A basis letter has word length at least its exponent.**  Its own exponent
sum already accounts for every letter of a shortest word. -/
theorem le_wordNorm_zpow_of {a b : α} (hab : a ≠ b) (n : ℤ) :
    n.natAbs ≤ wordNorm (freeAlphabet α) ((FreeGroup.of a) ^ n) := by
  have h := natAbs_add_natAbs_expVal_le (natAbs_basisWeight_add_le hab)
    ((FreeGroup.of a) ^ n)
  rw [expVal_zpow, expVal_zpow, expVal_of, expVal_of, basisWeight_self,
    basisWeight_of_ne (Ne.symm hab), mul_zero, mul_one] at h
  simpa using h

/-- **Two distinct basis letters do not cancel.**  The word length of `a⁻ⁿbᵐ` is
at least `|n| + |m|`, so the two axes separate at the identity. -/
theorem le_wordNorm_inv_mul {a b : α} (hab : a ≠ b) (n m : ℤ) :
    n.natAbs + m.natAbs ≤ wordNorm (freeAlphabet α)
      (((FreeGroup.of a) ^ n)⁻¹ * (FreeGroup.of b) ^ m) := by
  have h := natAbs_add_natAbs_expVal_le (natAbs_basisWeight_add_le hab)
    (((FreeGroup.of a) ^ n)⁻¹ * (FreeGroup.of b) ^ m)
  rw [expVal_mul, expVal_mul, expVal_inv, expVal_inv, expVal_zpow, expVal_zpow,
    expVal_zpow, expVal_zpow, expVal_of, expVal_of, expVal_of, expVal_of,
    basisWeight_self, basisWeight_self, basisWeight_of_ne hab,
    basisWeight_of_ne (Ne.symm hab)] at h
  simp only [mul_zero, mul_one, neg_zero, add_zero, zero_add] at h
  omega

/-- The basis alphabet of a free group, as an `Alphabet`. -/
def freeGroupAlphabet (α : Type) [DecidableEq α] : Alphabet (FreeGroup α) where
  carrier := freeAlphabet α
  symmetricGenerating := isSymmetricGeneratingSet_freeAlphabet

@[simp] theorem freeGroupAlphabet_carrier (α : Type) [DecidableEq α] :
    (freeGroupAlphabet α).carrier = freeAlphabet α := rfl

/-- **A basis letter is loxodromic**, with translation rate one: `|aⁿ| ≥ n`. -/
theorem isLoxodromic_of_basis {a b : α} (hab : a ≠ b) :
    IsLoxodromic (FreeGroup.of a) (Cayley.base (freeGroupAlphabet α)) := by
  refine ⟨1, one_pos, 0, le_rfl, ?_⟩
  intro k
  rw [dist_base_smul]
  have h := le_wordNorm_zpow_of hab (k : ℤ)
  rw [zpow_natCast] at h
  have h' : k ≤ wordNorm (freeAlphabet α) ((FreeGroup.of a) ^ k) := by simpa using h
  have h'' : (k : ℝ) ≤ (wordNorm (freeAlphabet α) ((FreeGroup.of a) ^ k) : ℝ) := by
    exact_mod_cast h'
  simp only [freeGroupAlphabet_carrier]
  linarith

/-- **Two distinct basis letters are independent**, with constant `0`: the
Gromov product of their power orbits at the identity vanishes. -/
theorem independent_of_basis {a b : α} (hab : a ≠ b) :
    Independent (FreeGroup.of a) (FreeGroup.of b)
      (Cayley.base (freeGroupAlphabet α)) := by
  refine ⟨0, ?_⟩
  intro n m
  have hup1 := wordNorm_zpow_le (isSymmetricGeneratingSet_freeAlphabet (α := α))
    (letterOf_mem (a, true)) n
  have hup2 := wordNorm_zpow_le (isSymmetricGeneratingSet_freeAlphabet (α := α))
    (letterOf_mem (b, true)) m
  have hlow := le_wordNorm_inv_mul hab n m
  have hkey : wordNorm (freeAlphabet α) ((FreeGroup.of a) ^ n)
      + wordNorm (freeAlphabet α) ((FreeGroup.of b) ^ m)
      ≤ wordNorm (freeAlphabet α)
        (((FreeGroup.of a) ^ n)⁻¹ * (FreeGroup.of b) ^ m) := by omega
  have hreal : ((wordNorm (freeAlphabet α) ((FreeGroup.of a) ^ n) : ℕ) : ℝ)
      + ((wordNorm (freeAlphabet α) ((FreeGroup.of b) ^ m) : ℕ) : ℝ)
      ≤ ((wordNorm (freeAlphabet α)
          (((FreeGroup.of a) ^ n)⁻¹ * (FreeGroup.of b) ^ m) : ℕ) : ℝ) := by
    exact_mod_cast hkey
  simp only [gromovProduct]
  rw [dist_smul_base_smul, dist_base_smul, dist_base_smul,
    dist_comm ((FreeGroup.of b) ^ m • Cayley.base (freeGroupAlphabet α))
      (Cayley.base (freeGroupAlphabet α)), dist_base_smul]
  simp only [freeGroupAlphabet_carrier]
  linarith

/-- **A free group of rank at least two is acylindrically hyperbolic.**  This is
the first instance of the class: the alphabet is the basis and its inverses, the
Cayley graph is a tree so `δ = 0`, the alphabet is finite so the action is
proper and hence acylindrical, and two distinct basis letters are independent
loxodromics. -/
theorem isAcylindricallyHyperbolic_freeGroup (α : Type) [Fintype α]
    [DecidableEq α] {a b : α} (hab : a ≠ b) :
    IsAcylindricallyHyperbolic (FreeGroup α) := by
  refine ⟨freeGroupAlphabet α, 0, ?_, ?_, ?_⟩
  · exact isHyperbolicSpace_zero_cayley
      (p := fun x y => ListPrefix.lcp x.toWord y.toWord) isTreeLike_freeAlphabet
  · refine isAcylindrical_cayley_of_finite _ ?_
    rw [freeGroupAlphabet_carrier, freeAlphabet]
    exact Set.finite_range _
  · exact ⟨FreeGroup.of a, Subgroup.mem_top _, FreeGroup.of b,
      Subgroup.mem_top _, isLoxodromic_of_basis hab,
      isLoxodromic_of_basis (Ne.symm hab), independent_of_basis hab⟩

/-- **The free group of rank two is acylindrically hyperbolic**, as an
instance. -/
instance instIsAcylindricallyHyperbolicFreeGroupFinTwo :
    IsAcylindricallyHyperbolic (FreeGroup (Fin 2)) :=
  isAcylindricallyHyperbolic_freeGroup (Fin 2) (a := 0) (b := 1) (by decide)

end FreeGroupAH

end GGT
end GroupApproximation
