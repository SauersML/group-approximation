import GroupApproximation.GGT.DGOBlockCycle
import GroupApproximation.GGT.DGOCorollary612Unconditional

/-!
# Dahmani--Guirardel--Osin's Corollary 6.12 in the form Hull's §5 consumes

`GGT.dgoCorollary612` produces *some* loxodromic element from a non-degenerate
hyperbolically embedded subgroup, which is what Osin's Lemma 5.12 asks for.
Hull's Lemma `nonelsub` and Lemma `yi` need four things that form does not
carry, and this module supplies three of them:

* a **threshold**: not *some* `h ∈ H_λ` works, but *every* `h` deep enough in
  `d̂_λ` --- which is what lets a consumer impose further conditions on the same
  element (Hull's Remark after `lox`);
* a **prescribed** `g`, rather than one the theorem chooses;
* an **arbitrary alphabet and index set**, `g` being spelled by a word rather
  than being a letter.

The fourth --- WPD of the produced element, and pairwise non-commensurability of
several of them --- is *not* here and is not reachable by this argument.  Both
are Dahmani--Guirardel--Osin's Lemma 4.21(b), which is proved by the isolated
component *counting* of their Proposition 4.14 with the constant uniform in the
number of sides.  The counting is what this route replaces, by a bound on a
single component in a short cycle, and that substitute stops being informative
exactly when the polygon grows --- which in 4.21(b) it does, after `h` has been
fixed.  See `GGT.DGOAlternatingCycle`'s header for the trade.

## The hypothesis on `g`

`g` is asked to be spelled by an admissible word `wg` **no letter of which is a
`lam`-letter**.  That covers both of Hull's call sites without a special case:
in `nonelsub` the alphabet is `𝒜 ⊔ E(h)` and `g ∈ ⟨𝒜⟩` is a word of base
letters; in `yi` the alphabet is `𝒜 ⊔ E(f₁) ⊔ … ⊔ E(f_k)` with `lam = k`, and
`g = a₁ ⋯ a_{k-1}` is spelled by `i`-letters with `i ≠ lam`.  It is what makes
the `h`-letters of `(wg h)^n` components of their own, and being syntactic it
does not care whether a base letter happens to lie in `H lam` as a group
element.

`0 < wg.length` is not a hypothesis: `wg = []` would spell `g = 1 ∈ H lam`,
which `hgH` excludes.

**This is a genuine restriction, and it is not Corollary 6.12 as printed.**
Dahmani--Guirardel--Osin ask only for `g ∈ G \ H`; `hno` asks for `g` to be
spellable *off* the coned subgroup, and the gap between the two is not empty.
Take `G = H ∗ ℤ` with `D.base = {t, t⁻¹}`, `D.fam lam = H`, and `g = h t` for
some `h ≠ 1`.  Then `g ∉ D.fam lam`, and `D.base ∪ H` is symmetric and
generates, so this is a legitimate `RelGenSet`; but a word of admissible letters
using no `lam`-letter spells an element of `⟨t⟩`, and `h t ∉ ⟨t⟩`, so **no `wg`
satisfying `hno` exists** and the theorem says nothing about that `g`.

What makes the restriction costless on Hull's route is that there the *base
alone* generates: `Alphabet G` carries `IsSymmetricGeneratingSet`, whose second
clause is that the letters generate, so every `g ∈ G` has a spelling by base
letters and `hno` is automatic.  A consumer holding only `RelGenSet`'s weaker
clause --- that `base ∪ ⋃ fam` generates --- does not get that, and should not
cite this as 6.12.  `GGT.dgoCorollary612` is the unrestricted statement, at the
cost of choosing its own `g` in `D.base`.

## Two forms of the threshold

The cycle argument spells the letter `h` and Dahmani--Guirardel--Osin's Lemma 4.6
returns the *inverse* span, so the primitive is stated with `h⁻¹` outside the
ball.  `exists_threshold_isLoxodromic_mul_of_symm` is the form a consumer wants,
`h` itself outside the ball, and costs the symmetry of `D.base` --- which every
`Alphabet` carries, symmetry being a field of `IsSymmetricGeneratingSet`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT.OsinComponents

universe u w

section Threshold

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Every sufficiently deep `h` makes `g h` loxodromic.**

Dahmani--Guirardel--Osin's Theorem 6.11 in the shape Hull's §5 consumes: `g` is
given, `Λ` and the alphabet are arbitrary, and the conclusion holds for *every*
`h ∈ H lam` beyond a threshold that depends only on the hyperbolicity constant
and on the length of the spelling of `g`.

The threshold is stated on `h⁻¹`; see
`exists_threshold_isLoxodromic_mul_of_symm` for the form with `h` itself.  Local
finiteness of `d̂` is not used, only hyperbolicity of `Γ(G, X ⊔ ℋ)`, which is why
the hypothesis is that and not `↪_h`.  Unboundedness of `d̂_λ` is not a
hypothesis either: it is how a consumer knows a deep `h` exists, not something
the implication needs, and `exists_isLoxodromic_mul_of_unbounded` below is the
form that produces one. -/
theorem exists_threshold_isLoxodromic_mul (D : RelGenSet G Λ) (lam : Λ)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    {g : G} (hgH : g ∉ D.fam lam) (wg : List (RelLetter G Λ))
    (hlet : ∀ c ∈ wg, D.IsLetter c) (hval : RelLetter.listVal wg = g)
    (hno : ∀ c ∈ wg, ¬ c.IsCompOf lam) :
    ∃ N : ℕ, ∀ h ∈ D.fam lam, h⁻¹ ∉ D.relBall lam N →
      IsLoxodromic (g * h) (Cayley.base D.alphabet) := by
  -- the spelling is nonempty, since `g ∉ H lam`
  have hr : 0 < wg.length := by
    rcases Nat.eq_zero_or_pos wg.length with h0 | h0
    · exfalso
      have hnil : wg = [] := List.length_eq_zero_iff.mp h0
      rw [hnil] at hval
      rw [← hval] at hgH
      exact hgH (by simp [RelLetter.listVal])
    · exact h0
  have hgHval : RelLetter.listVal wg ∉ D.fam lam := by rw [hval]; exact hgH
  -- hyperbolicity, normalised to a nonnegative constant
  obtain ⟨δ₀, hδ₀⟩ := hhyp
  set δ : ℝ := max δ₀ 0
  have hδ0 : 0 ≤ δ := le_max_right _ _
  have hδle : δ₀ ≤ δ := le_max_left _ _
  have hδ : IsHyperbolicSpace δ (Cayley D.alphabet) := by
    intro y z t v
    have hh := hδ₀ y z t v
    linarith
  -- the dyadic exponent and the radius the window needs
  obtain ⟨J, hJ⟩ :=
    (eventually_affine_lt_pow_two (2 * δ) (((wg.length : ℝ) + 1) + 1)).exists
  set N₀ : ℕ := 2 ^ J with hN₀
  set R : ℕ := N₀ * (wg.length + 2) with hR
  refine ⟨R, ?_⟩
  intro h hh hnb
  have hiso : IsIsometricAction G (Cayley D.alphabet) :=
    isIsometricAction_cayley D.alphabet
  set x : Cayley D.alphabet := Cayley.base D.alphabet with hxdef
  have hFdist : ∀ n : ℕ, dist x (((g * h) ^ n) • x)
      = (wordDist D.alphabet.carrier 1 ((g * h) ^ n) : ℝ) := by
    intro n
    simp [hxdef]
  -- the window bound
  have hlow : ∀ n : ℕ, 1 ≤ n → n ≤ N₀ →
      (n : ℝ) - 1 ≤ (wordDist D.alphabet.carrier 1 ((g * h) ^ n) : ℝ) := by
    intro n hn1 hnN
    have hwin : n * (wg.length + 2) ≤ R + 1 := by
      have := Nat.mul_le_mul_right (wg.length + 2) hnN
      omega
    have hnat := sub_one_le_wordDist_block D lam hlet hno hr hgHval hh hnb hwin
    rw [hval] at hnat
    have hcast : ((n - 1 : ℕ) : ℝ)
        ≤ (wordDist D.alphabet.carrier 1 ((g * h) ^ n) : ℝ) := by
      exact_mod_cast hnat
    rwa [Nat.cast_sub hn1, Nat.cast_one] at hcast
  -- the one-step bound
  have hF1 : (wordDist D.alphabet.carrier 1 ((g * h) ^ 1) : ℝ)
      ≤ (wg.length : ℝ) + 1 := by
    rw [pow_one]
    have hg1 : wordNorm D.alphabet.carrier g ≤ wg.length := by
      rw [← hval]
      exact wordNorm_listVal_le D wg hlet
    have hh1 : wordNorm D.alphabet.carrier h ≤ 1 :=
      wordNorm_le_one_of_mem (D.fam_subset_alphabet lam hh)
    have hmul := wordNorm_mul_le D.alphabet.symmetricGenerating g h
    have hle : wordDist D.alphabet.carrier 1 (g * h) ≤ wg.length + 1 := by
      rw [wordDist_one_left]
      omega
    have hcast : ((wordDist D.alphabet.carrier 1 (g * h) : ℕ) : ℝ)
        ≤ ((wg.length + 1 : ℕ) : ℝ) := by exact_mod_cast hle
    push_cast at hcast
    exact hcast
  -- the doubling gap
  obtain ⟨K, hK0, hKgap⟩ := exists_dyadic_gap
    (fun n => wordDist D.alphabet.carrier 1 ((g * h) ^ n)) δ ((wg.length : ℝ) + 1)
    J N₀ hF1 hlow (by omega) hJ
  have hpow2 : ((g * h) ^ K) ^ 2 = (g * h) ^ (2 * K) := by
    rw [← pow_mul]
    congr 1
    omega
  have hloxK : IsLoxodromic ((g * h) ^ K) x := by
    refine isLoxodromic_of_two_step_gap hδ hiso hδ0 ?_
    rw [hpow2, hFdist (2 * K), hFdist K]
    exact hKgap
  exact isLoxodromic_of_pow_isLoxodromic hiso hK0 hloxK

/-- **Some `g h` is loxodromic**, for a consumer that has unboundedness rather
than a particular deep `h`.  This is `GGT.dgoCorollary612`'s shape at a general
`g` and alphabet; the deep element is produced from `hunb`, and inverted because
the threshold is stated on `h⁻¹`. -/
theorem exists_isLoxodromic_mul_of_unbounded (D : RelGenSet G Λ) (lam : Λ)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    (hunb : ∀ n : ℕ, ¬ ((D.fam lam : Subgroup G) : Set G) ⊆ D.relBall lam n)
    {g : G} (hgH : g ∉ D.fam lam) (wg : List (RelLetter G Λ))
    (hlet : ∀ c ∈ wg, D.IsLetter c) (hval : RelLetter.listVal wg = g)
    (hno : ∀ c ∈ wg, ¬ c.IsCompOf lam) :
    ∃ h ∈ D.fam lam, IsLoxodromic (g * h) (Cayley.base D.alphabet) := by
  obtain ⟨N, hN⟩ :=
    exists_threshold_isLoxodromic_mul D lam hhyp hgH wg hlet hval hno
  obtain ⟨k, hkH, hkball⟩ : ∃ k : G, k ∈ D.fam lam ∧ k ∉ D.relBall lam N := by
    by_contra hcon
    push Not at hcon
    exact hunb N (fun y hy => hcon y hy)
  exact ⟨k⁻¹, inv_mem hkH, hN k⁻¹ (inv_mem hkH) (by rwa [inv_inv])⟩

/-- **The threshold, on `h` rather than on `h⁻¹`.**  At a symmetric base the
relative balls are closed under inversion, so the two conditions agree.  Every
`Alphabet` is symmetric by construction; a `RelGenSet` need not be, and
`OsinTheorem54SepSymmetric.exists_symmetric_base` supplies one that is. -/
theorem exists_threshold_isLoxodromic_mul_of_symm (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ y ∈ D.base, y⁻¹ ∈ D.base)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    {g : G} (hgH : g ∉ D.fam lam) (wg : List (RelLetter G Λ))
    (hlet : ∀ c ∈ wg, D.IsLetter c) (hval : RelLetter.listVal wg = g)
    (hno : ∀ c ∈ wg, ¬ c.IsCompOf lam) :
    ∃ N : ℕ, ∀ h ∈ D.fam lam, h ∉ D.relBall lam N →
      IsLoxodromic (g * h) (Cayley.base D.alphabet) := by
  obtain ⟨N, hN⟩ :=
    exists_threshold_isLoxodromic_mul D lam hhyp hgH wg hlet hval hno
  refine ⟨N, ?_⟩
  intro h hh hnb
  refine hN h hh ?_
  intro hcon
  have hinv := relBall_inv D lam hsymm hcon
  rw [inv_inv] at hinv
  exact hnb hinv

end Threshold

end GGT
end GroupApproximation
