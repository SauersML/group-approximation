import Mathlib.GroupTheory.HNNExtension
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Sofic.ConcreteCompressionSource

/-!
# Torsion in HNN extensions: the Britton power theorem and the reduction

The torsion theorem for HNN extensions says that a torsion-free base
yields a torsion-free extension, because every finite-order element is
conjugate into the base.  This file proves the two halves of that
statement that are pure Britton combinatorics over the normal-form
machinery Mathlib already certifies, and isolates the remaining half —
cyclic-reduction existence — as one named interface.

* **The Britton power theorem** (`CyclicWord.elem_pow_ne_one`): a
  cyclically reduced word with at least one stable letter has infinite
  order.  A cyclic word is recorded head-absorbed, so its powers are
  literal concatenations of its letter list; the chain condition of the
  concatenation is the cyclic seam condition, and Britton's lemma
  (`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`) refuses a
  nonempty reduced word inside the base copy.
* **The reduction** (`isPowerTorsionFree_of_existsCyclicConjugate`): if
  every element is conjugate into the base or to a cyclic word, then
  torsion-freeness of the base passes to the extension — the base case
  by injectivity of the base copy, the cyclic case by the power
  theorem.
* **The stable-letter grading** (`lengthHom`): the homomorphism to the
  integers counting stable letters, giving immediately that every
  element off its kernel has infinite order.

The interface `ExistsCyclicConjugate` — every element of the HNN
extension is conjugate into the base or to a cyclic word — is the
classical cyclic-reduction existence lemma.  The theorems below take it
as a named hypothesis rather than an axiom.

**It is no longer an unformalized input.**  `GroupTheory/HNNBrittonCyclic.lean`
proves it outright, from Mathlib's normal-form theory for HNN extensions,
as `HNNBritton.existsCyclicConjugate`; the unconditional torsion theorem
is `HNNBritton.isPowerTorsionFree_hnn`, and the affine-skeleton
corollaries are `HNNBritton.isPowerTorsionFree_sourceGroup` and
`HNNBritton.isPowerTorsionFree_integerSourceGroup`.  That file imports
this one, so the conditional statements here cannot call it without a
cycle; they are kept as the abstract form, and the declarations named
above supersede them one for one.  Nothing in this file is on the trust
surface: prefer the `HNNBritton` versions at every use site.
-/

namespace GroupApproximation
namespace HNNTorsionFree

universe u

/-! ## Concatenation powers of a letter list -/

/-- The `n`-fold concatenation of a list. -/
def concatN {X : Type*} : ℕ → List X → List X
  | 0, _ => []
  | n + 1, L => L ++ concatN n L

private theorem concatN_ne_nil {X : Type*} {L : List X} (hL : L ≠ [])
    {n : ℕ} (hn : n ≠ 0) : concatN n L ≠ [] := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
    show L ++ concatN m L ≠ []
    cases L with
    | nil => exact absurd rfl hL
    | cons x xs => simp

private theorem head?_concatN_succ {X : Type*} {L : List X} (hL : L ≠ [])
    (n : ℕ) : (concatN (n + 1) L).head? = L.head? := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    show ((x :: xs) ++ concatN n (x :: xs)).head? = _
    simp

private theorem isChain_concatN {X : Type*} {R : X → X → Prop} {L : List X}
    (hL : L ≠ []) (hchain : List.IsChain R L)
    (hcyc : ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, R x y) (n : ℕ) :
    List.IsChain R (concatN n L) := by
  induction n with
  | zero =>
    show List.IsChain R []
    exact List.isChain_nil
  | succ m ih =>
    show List.IsChain R (L ++ concatN m L)
    refine List.IsChain.append hchain ih ?_
    intro x hx y hy
    cases m with
    | zero =>
      simp [concatN] at hy
    | succ k =>
      rw [head?_concatN_succ hL k] at hy
      exact hcyc x hx y hy

private theorem prod_concatN {X M : Type*} [Monoid M] (f : X → M)
    (L : List X) (n : ℕ) :
    ((concatN n L).map f).prod = ((L.map f).prod) ^ n := by
  induction n with
  | zero => simp [concatN]
  | succ m ih =>
    show ((L ++ concatN m L).map f).prod = _
    rw [List.map_append, List.prod_append, ih, pow_succ']

private theorem conj_pow_eq {H : Type*} [Group H] (g a : H) :
    ∀ n : ℕ, (g * a * g⁻¹) ^ n = g * a ^ n * g⁻¹
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, conj_pow_eq g a n, pow_succ]
    group

/-! ## Cyclic words and the Britton power theorem -/

variable {G : Type u} [Group G] {A B : Subgroup G}

/-- A head-absorbed cyclically reduced word: a nonempty letter list
whose chain condition also holds around the seam.  Powers of such a
word are spelled by literal concatenations of the letter list, so the
seam condition is exactly what keeps every power Britton-reduced. -/
structure CyclicWord (G : Type u) [Group G] (A B : Subgroup G) :
    Type u where
  /-- The letters: signs of the stable letter and base elements. -/
  letters : List (ℤˣ × G)
  /-- At least one stable letter occurs. -/
  nonempty : letters ≠ []
  /-- The Britton chain condition along the word. -/
  chain : List.IsChain
    (fun a b : ℤˣ × G =>
      a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1) letters
  /-- The Britton chain condition around the seam. -/
  cyclic : ∀ x ∈ letters.getLast?, ∀ y ∈ letters.head?,
    (x.2 ∈ HNNExtension.toSubgroup A B x.1 → x.1 = y.1)

/-- The element of the HNN extension spelled by a cyclic word. -/
def CyclicWord.elem (φ : A ≃* B) (c : CyclicWord G A B) :
    HNNExtension G A B φ :=
  (c.letters.map fun x =>
    HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod

/-- **The Britton power theorem.**  A cyclically reduced word with at
least one stable letter has infinite order: its `n`-th power is spelled
by the `n`-fold concatenation of its letter list, which the seam
condition keeps Britton-reduced, and Britton's lemma refuses a nonempty
reduced word that lands in the base copy. -/
theorem CyclicWord.elem_pow_ne_one (φ : A ≃* B) (c : CyclicWord G A B)
    {n : ℕ} (hn : n ≠ 0) : c.elem φ ^ n ≠ 1 := by
  intro hpow
  have hchain := isChain_concatN c.nonempty c.chain c.cyclic n
  have hmem : (HNNExtension.NormalWord.ReducedWord.mk (1 : G)
      (concatN n c.letters) hchain).prod φ ∈
      (HNNExtension.of : G →* HNNExtension G A B φ).range := by
    show HNNExtension.of (1 : G) *
        ((concatN n c.letters).map fun x =>
          HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod ∈ _
    rw [map_one, one_mul, prod_concatN]
    rw [show ((c.letters.map fun x =>
        HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod) =
      c.elem φ from rfl]
    rw [hpow]
    exact ⟨1, map_one _⟩
  have hnil :=
    HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ _ hmem
  exact concatN_ne_nil c.nonempty hn hnil

/-! ## The reduction to cyclic-reduction existence -/

/-- **The cyclic-reduction interface**: every element of the HNN
extension is conjugate into the base copy or conjugate to a cyclically
reduced word.  This is the classical cyclic-reduction existence lemma.

It is **proved**, not assumed: `HNNBritton.existsCyclicConjugate` in
`GroupTheory/HNNBrittonCyclic.lean` supplies it for every `φ`.  The
predicate survives here only because that file imports this one, so the
theorems below cannot invoke it without a cycle; they take it as a
hypothesis and are superseded one for one by the `HNNBritton`
declarations.  Do not describe it as an unformalized input. -/
def ExistsCyclicConjugate (φ : A ≃* B) : Prop :=
  ∀ x : HNNExtension G A B φ,
    (∃ (g : HNNExtension G A B φ) (b : G),
      x = g * HNNExtension.of b * g⁻¹) ∨
    (∃ (g : HNNExtension G A B φ) (c : CyclicWord G A B),
      x = g * c.elem φ * g⁻¹)

/-- **The torsion theorem, modulo cyclic reduction.**  If every element
is conjugate into the base or to a cyclic word, then torsion-freeness
of the base passes to the HNN extension: conjugates into the base are
controlled by injectivity of the base copy, and cyclic words have
infinite order by the Britton power theorem. -/
theorem isPowerTorsionFree_of_existsCyclicConjugate (φ : A ≃* B)
    (hcyc : ExistsCyclicConjugate φ) (hG : IsPowerTorsionFree G) :
    IsPowerTorsionFree (HNNExtension G A B φ) := by
  intro x n hn hx
  rcases hcyc x with ⟨g, b, rfl⟩ | ⟨g, c, rfl⟩
  · have h0 : g * HNNExtension.of b ^ n * g⁻¹ = 1 := by
      rw [← conj_pow_eq]
      exact hx
    have h2 : (HNNExtension.of b : HNNExtension G A B φ) ^ n = 1 := by
      have h3 := congrArg (fun z => g⁻¹ * z * g) h0
      simpa [mul_assoc] using h3
    have h1 : HNNExtension.of (b ^ n) =
        (1 : HNNExtension G A B φ) := by
      rw [map_pow]
      exact h2
    have hbn : b ^ n = 1 :=
      HNNExtension.of_injective φ (by rw [h1, map_one])
    have hb : b = 1 := hG b n hn hbn
    rw [hb]
    simp
  · exfalso
    apply CyclicWord.elem_pow_ne_one φ c hn.ne'
    have h0 : g * c.elem φ ^ n * g⁻¹ = 1 := by
      rw [← conj_pow_eq]
      exact hx
    have h3 := congrArg (fun z => g⁻¹ * z * g) h0
    simpa [mul_assoc] using h3

/-! ## The stable-letter grading -/

variable (φ : A ≃* B)

/-- The homomorphism to the integers counting stable letters. -/
def lengthHom : HNNExtension G A B φ →* Multiplicative ℤ :=
  HNNExtension.lift 1 (Multiplicative.ofAdd 1) (fun _ => by simp)

@[simp] theorem lengthHom_of (g : G) :
    lengthHom φ (HNNExtension.of g) = 1 := by
  simp [lengthHom, HNNExtension.lift_of]

@[simp] theorem lengthHom_t :
    lengthHom φ (HNNExtension.t : HNNExtension G A B φ) =
      Multiplicative.ofAdd 1 := by
  simp [lengthHom, HNNExtension.lift_t]

/-- Every element off the kernel of the stable-letter grading has
infinite order. -/
theorem pow_ne_one_of_lengthHom_ne_one {x : HNNExtension G A B φ}
    (hx : lengthHom φ x ≠ 1) {n : ℕ} (hn : 0 < n) : x ^ n ≠ 1 := by
  intro h
  apply hx
  apply ConcreteCompressionSource.isPowerTorsionFree_multiplicative_int
    (lengthHom φ x) n hn
  rw [← map_pow, h, map_one]

/-- The stable letter has infinite order in every HNN extension. -/
theorem t_pow_ne_one {n : ℕ} (hn : 0 < n) :
    (HNNExtension.t : HNNExtension G A B φ) ^ n ≠ 1 :=
  pow_ne_one_of_lengthHom_ne_one φ
    (by
      rw [lengthHom_t]
      intro hc
      have h1 := congrArg Multiplicative.toAdd hc
      simp only [toAdd_ofAdd, toAdd_one] at h1
      exact one_ne_zero h1) hn

/-! ## The affine compression skeleton -/

/-- Torsion-freeness of the affine HNN source, conditional on the
cyclic-reduction interface at its datum. -/
theorem isPowerTorsionFree_sourceGroup_of_existsCyclicConjugate
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    (h : ExistsCyclicConjugate (ConcreteCompressionSource.sourceEquiv α hα))
    (hbase : IsPowerTorsionFree (ConcreteCompressionSource.Base Γ)) :
    IsPowerTorsionFree (ConcreteCompressionSource.SourceGroup α hα) :=
  isPowerTorsionFree_of_existsCyclicConjugate _ h hbase

/-- Torsion-freeness of the explicit integer source, conditional on the
cyclic-reduction interface: the base side is already certified. -/
theorem isPowerTorsionFree_integerSourceGroup_of_existsCyclicConjugate
    (h : ExistsCyclicConjugate (ConcreteCompressionSource.sourceEquiv
      ConcreteCompressionSource.doubling
      ConcreteCompressionSource.doubling_injective)) :
    IsPowerTorsionFree (ConcreteCompressionSource.SourceGroup
      ConcreteCompressionSource.doubling
      ConcreteCompressionSource.doubling_injective) :=
  isPowerTorsionFree_sourceGroup_of_existsCyclicConjugate _ _ h
    ConcreteCompressionSource.base_isPowerTorsionFree

end HNNTorsionFree
end GroupApproximation
