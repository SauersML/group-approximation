import GroupApproximation.GGT.DGOAlternatingCycle
import GroupApproximation.GGT.DGOCorollary612Malnormal

/-!
# Dahmani--Guirardel--Osin's Corollary 6.12, proved

> **Corollary 6.12** (p. 93).  Let `G` be a group, `X ⊆ G`, `H ↪_h (G,X)` a
> non-degenerate subgroup.  Then for every `a ∈ G \ H` there exists `h ∈ H` such
> that `ah` is loxodromic and satisfies WPD with respect to the action on
> `Γ(G, X ⊔ H)`.

`GGT.DGOCorollary612` records the loxodromy half, which is all Osin's Lemma 5.12
consumes, and `dgoCorollary612` proves it.  So `osinTheorem12_of_two` obtains
`OsinTheorem12` from `DGOTheorem68` and `OsinTheorem54` alone.

The same argument proves more, and `dgoTheorem611'` records it: their
**Theorem 6.11** itself, in its loxodromy form, for every `a ∈ X` outside
`H_λ`.  The hypothesis `a ∉ H_λ` is not in their statement and has to be added
--- without it the statement is false, which
`GGT.DGOTheorem611Refutation.not_dgoTheorem611` proves --- but it is in their
proof, as condition `(W3)` of their Lemma 4.21, and every use of Theorem 6.11
supplies it.

## Why this is not their proof

Their route is Theorem 6.11, and its loxodromy clause is Lemma 4.21(a): the word
`(ah)^N` satisfies conditions `(W1)`--`(W3)`, so the path it labels is
`(4,1)`-quasi-geodesic.  Lemma 4.21(a) counts the components of that path that
are isolated in the geodesic `(2m+2)`-gon obtained by closing it with a
geodesic, and bounds their number using Proposition 4.14 --- the linear
isolated-component bound *at an arbitrary number of sides*.  This repository has
that bound only at `n ≤ 6`
(`DGOPolygonBaseCaseTower.isolatedComponentBound_of_fourPointHyperbolic`), and
Lemma 4.17 cannot extend it: its constant grows with the number of sides.

The proof here uses no polygon theory at all.  Its two inputs are their
Lemma 4.6 --- an isolated component of a cycle of length `C` has `d̂ ≤ C`,
`OsinComponents.relBall_inv_of_isolated_of_closed`, unconditional --- and the
hyperbolicity of `Γ(G, X ⊔ ℋ)`, used only through
`HullGeometry.isLoxodromic_of_local_backtracking`.

## The shape of the argument

`GGT.DGOAlternatingCycle.sub_one_le_wordDist` is the geometry: with `a ∈ X \ H`
and `h ∈ H` whose inverse is outside the `d̂`-ball of radius `R`,

    n - 1 ≤ |(a h)^n|      for every  3n ≤ R + 1.

Lemma 4.6 alone cannot push this past `n ≈ R/3`: once the cycle it builds is
longer than `R`, an isolated component tells one nothing.  What replaces the
missing uniformity is that `R` may be taken as large as one likes, and a window
of length `2^J` is already enough, because displacement along a chain either
doubles somewhere or stays affine:

* if `|(a h)^{2K}| ≤ |(a h)^K| + 2δ` for every dyadic `K` up to `2^J`, then
  `|(a h)^{2^J}| ≤ 2 + 2δJ`, while the window bound gives `|(a h)^{2^J}| ≥ 2^J - 1`;
* `HullGeometry.eventually_affine_lt_pow_two` says `2^J` outgrows `3 + 2δJ`, so
  some `K` has `|(a h)^{2K}| > |(a h)^K| + 2δ`.

That single inequality is exactly the hypothesis of the local-to-global estimate
`HullGeometry.isLoxodromic_of_local_backtracking` at `p = (a h)^K`: the turn
`(x | p²x)_{px}` equals `|p| - |p²|/2`, and `2((|p| - |p²|/2) + δ) < |p|` is the
same inequality.  So `(a h)^K` is loxodromic, hence `a h` is.

## Where each hypothesis is spent

`a ∉ H` is spent once, in `DGOAlternatingCycle`: it is what makes consecutive
`H`-letters of `(a h)^n` unconnected, which is Dahmani--Guirardel--Osin's
condition `(W3)`.  Non-degeneracy is spent twice: `H ≠ ⊤` supplies the letter
`a` (`exists_mem_base_notMem_fam`), and `H` infinite supplies, through local
finiteness, an element of `H` outside any prescribed ball
(`not_subset_relBall_of_infinite`).  Hyperbolicity is spent only in the last
step.  Nothing needs `X` symmetric: the letter placed in the cycle is `h` while
the element kept far from `1` is `h⁻¹`, and Lemma 4.6 in the form that bounds the
inverse span holds at any base.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT.OsinComponents

universe u v

/-! ## One doubling gap certifies loxodromy -/

section Gap

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **An element whose square outruns it by more than `2δ` is loxodromic.**

The Gromov product at the middle vertex of `x, p x, p² x` is
`|p| - |p²|/2`, so `2((|p| - |p²|/2) + δ) < |p|` is exactly
`|p²| > |p| + 2δ`, and `HullGeometry.isLoxodromic_of_local_backtracking` then
propagates the turn along the whole orbit.  The nonnegativity clause is free:
`|p²| ≤ 2|p|` by subadditivity. -/
theorem isLoxodromic_of_two_step_gap {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) (hδ0 : 0 ≤ δ) {p : G} {x : X}
    (hgap : dist x (p • x) + 2 * δ < dist x ((p ^ 2) • x)) :
    IsLoxodromic p x := by
  have hmid : dist ((p ^ 2) • x) (p • x) = dist x (p • x) := by
    have h := hiso p x (p • x)
    rw [← mul_smul, ← pow_two] at h
    rw [dist_comm]
    exact h
  have hturn : gromovProduct x ((p ^ 2) • x) (p • x)
      = dist x (p • x) - dist x ((p ^ 2) • x) / 2 := by
    unfold gromovProduct
    rw [hmid]
    ring
  have hBle : dist x ((p ^ 2) • x) ≤ 2 * dist x (p • x) := by
    have hsub := dist_pow_le hiso p x 2
    push_cast at hsub
    linarith
  refine isLoxodromic_of_local_backtracking hδ hiso
    (C := dist x (p • x) - dist x ((p ^ 2) • x) / 2) ?_ ?_ (le_of_eq hturn)
  · linarith
  · linarith

end Gap

/-! ## The dyadic bootstrap -/

/-- **Affine growth on a dyadic window is impossible.**

If a subadditive-looking `F` is at least `n - 1` on `[1, N]`, is at most `2` at
`1`, and never gains more than `2δ` on doubling inside the window, then along the
powers of two it is at most `2 + 2δj`, which `2^J - 1` outgrows.  So some
doubling inside the window does gain more than `2δ`. -/
theorem exists_dyadic_gap (F : ℕ → ℕ) (δ : ℝ) (J N : ℕ)
    (hF1 : (F 1 : ℝ) ≤ 2)
    (hlow : ∀ n : ℕ, 1 ≤ n → n ≤ N → (n : ℝ) - 1 ≤ (F n : ℝ))
    (hJN : 2 ^ J ≤ N) (hJ : 2 * δ * J + 3 < (2 : ℝ) ^ J) :
    ∃ K : ℕ, 0 < K ∧ (F K : ℝ) + 2 * δ < (F (2 * K) : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j : ℕ, 2 ^ j ≤ N →
      (F (2 ^ j) : ℝ) ≤ (F 1 : ℝ) + j * (2 * δ) := by
    intro j
    induction j with
    | zero =>
        intro _
        simp
    | succ i ih =>
        intro hle
        have hdouble : 2 * 2 ^ i = 2 ^ (i + 1) := by ring
        have hle' : 2 * 2 ^ i ≤ N := by rw [hdouble]; exact hle
        have hpos : 0 < 2 ^ i := by positivity
        have hi : 2 ^ i ≤ N := by omega
        have hIH := ih hi
        have hc := hcon (2 ^ i) hpos
        rw [hdouble] at hc
        push_cast
        linarith
  have hlowJ := hlow (2 ^ J) (Nat.one_le_pow J 2 (by norm_num)) hJN
  have hupJ := hstep J hJN
  have hcast : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; ring
  rw [hcast] at hlowJ
  linarith

/-! ## Corollary 6.12 -/

section Main

variable {G : Type u} [Group G]

/-- **For every letter of `X` outside `H`, some `a h` is loxodromic.**

This is the loxodromy conclusion of Dahmani--Guirardel--Osin's Theorem 6.11,
with the hypothesis their statement omits: `a ∉ H`.  Without it the statement is
false --- `GGT.DGOTheorem611Refutation` exhibits the model --- and their own
proof needs it, to get condition `(W3)` of their Lemma 4.21.

Two of their hypotheses are not used.  The finite intersection `|H^a ∩ H| < ∞`
is not: it enters their proof only through the WPD conclusion, which is dropped
here.  And local finiteness of `d̂` is not: only the hyperbolicity of
`Γ(G, X ⊔ ℋ)` is, which is why the hypothesis is stated as that and not as
`↪_h`. -/
theorem exists_isLoxodromic_mul_of_notMem_fam (D : RelGenSet G Unit)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    (hunb : ∀ n : ℕ, ¬ ((D.fam () : Subgroup G) : Set G) ⊆ D.relBall () n)
    {a : G} (haB : a ∈ D.base) (haH : a ∉ D.fam ()) :
    ∃ h ∈ D.fam (), IsLoxodromic (a * h) (Cayley.base D.alphabet) := by
  -- hyperbolicity, normalised to a nonnegative constant
  obtain ⟨δ₀, hδ₀⟩ := hhyp
  set δ : ℝ := max δ₀ 0
  have hδ0 : 0 ≤ δ := le_max_right _ _
  have hδle : δ₀ ≤ δ := le_max_left _ _
  have hδ : IsHyperbolicSpace δ (Cayley D.alphabet) := by
    intro w y z t
    have h := hδ₀ w y z t
    linarith
  -- the dyadic exponent, and the radius the window needs
  obtain ⟨J, hJ⟩ := (eventually_affine_lt_pow_two (2 * δ) 3).exists
  set N : ℕ := 2 ^ J with hNdef
  set R : ℕ := 3 * N with hRdef
  -- an element of `H` whose inverse is outside the ball of radius `R`
  obtain ⟨k, hkH, hkball⟩ : ∃ k : G, k ∈ D.fam () ∧ k ∉ D.relBall () R := by
    by_contra hcon
    push Not at hcon
    exact hunb R (fun y hy => hcon y hy)
  have hhH : k⁻¹ ∈ D.fam () := inv_mem hkH
  have hnb : (k⁻¹)⁻¹ ∉ D.relBall () R := by rwa [inv_inv]
  set x : Cayley D.alphabet := Cayley.base D.alphabet with hxdef
  have hiso : IsIsometricAction G (Cayley D.alphabet) :=
    isIsometricAction_cayley D.alphabet
  have hFdist : ∀ n : ℕ, dist x (((a * k⁻¹) ^ n) • x)
      = (wordDist D.alphabet.carrier 1 ((a * k⁻¹) ^ n) : ℝ) := by
    intro n
    simp [hxdef]
  -- the window bound
  have hlow : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (n : ℝ) - 1 ≤ (wordDist D.alphabet.carrier 1 ((a * k⁻¹) ^ n) : ℝ) := by
    intro n hn1 hnN
    have hnat := sub_one_le_wordDist D haB haH hhH hnb (n := n) (by omega)
    have hcast : ((n - 1 : ℕ) : ℝ)
        ≤ (wordDist D.alphabet.carrier 1 ((a * k⁻¹) ^ n) : ℝ) := by
      exact_mod_cast hnat
    rwa [Nat.cast_sub hn1, Nat.cast_one] at hcast
  -- the one-letter bound
  have hF1 : (wordDist D.alphabet.carrier 1 ((a * k⁻¹) ^ 1) : ℝ) ≤ 2 := by
    rw [pow_one]
    have ha1 : wordNorm D.alphabet.carrier a ≤ 1 :=
      wordNorm_le_one_of_mem (Set.mem_union_left _ haB)
    have hk1 : wordNorm D.alphabet.carrier k⁻¹ ≤ 1 :=
      wordNorm_le_one_of_mem (D.fam_subset_alphabet () hhH)
    have hmul := wordNorm_mul_le D.alphabet.symmetricGenerating a k⁻¹
    have hle : wordDist D.alphabet.carrier 1 (a * k⁻¹) ≤ 2 := by
      rw [wordDist_one_left]
      omega
    exact_mod_cast hle
  -- the doubling gap
  obtain ⟨K, hK0, hKgap⟩ := exists_dyadic_gap
    (fun n => wordDist D.alphabet.carrier 1 ((a * k⁻¹) ^ n)) δ J N hF1 hlow
    (by omega) hJ
  -- and loxodromy
  have hpow2 : ((a * k⁻¹) ^ K) ^ 2 = (a * k⁻¹) ^ (2 * K) := by
    rw [← pow_mul]
    congr 1
    omega
  have hloxK : IsLoxodromic ((a * k⁻¹) ^ K) x := by
    refine isLoxodromic_of_two_step_gap hδ hiso hδ0 ?_
    rw [hpow2, hFdist (2 * K), hFdist K]
    exact hKgap
  exact ⟨k⁻¹, hhH, isLoxodromic_of_pow_isLoxodromic hiso hK0 hloxK⟩

/-- **A non-degenerate hyperbolically embedded subgroup makes some element
loxodromic on `Γ(G, X ⊔ H)`.**  This is Dahmani--Guirardel--Osin's
Corollary 6.12 in the form Osin's Lemma 5.12 quotes it: `H ≠ ⊤` supplies the
letter `a`, and `H` infinite supplies, through local finiteness, the unbounded
`d̂`. -/
theorem exists_isLoxodromic_of_isHyperbolicallyEmbedded (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded) (hnd : IsNonDegenerate (D.fam ())) :
    ∃ g : G, IsLoxodromic g (Cayley.base D.alphabet) := by
  obtain ⟨a, haB, haH⟩ := exists_mem_base_notMem_fam D hnd.1
  obtain ⟨h, -, hlox⟩ := exists_isLoxodromic_mul_of_notMem_fam D hemb.hyperbolic
    (not_subset_relBall_of_infinite D hemb hnd.2) haB haH
  exact ⟨a * h, hlox⟩

end Main

/-- **Dahmani--Guirardel--Osin's Theorem 6.11, repaired and proved**, in the
loxodromy form `DGOTheorem611` records --- with the hypothesis `a ∉ H_λ` that
their statement omits and their proof needs.  The finite-intersection clause is
kept, so that this is literally `DGOTheorem611` plus one hypothesis, but it is
not used.

`GGT.DGOTheorem611Refutation.not_dgoTheorem611` shows the added hypothesis
cannot be dropped. -/
theorem dgoTheorem611' : ∀ (G : Type u) [Group G] (D : RelGenSet G Unit),
    D.IsHyperbolicallyEmbedded →
      (∀ n : ℕ, ¬ ((D.fam () : Subgroup G) : Set G) ⊆ D.relBall () n) →
        ∀ a ∈ D.base, a ∉ D.fam () →
          {h : G | h ∈ D.fam () ∧ a⁻¹ * h * a ∈ D.fam ()}.Finite →
            ∃ h ∈ D.fam (), IsLoxodromic (a * h) (Cayley.base D.alphabet) := by
  intro G _ D hemb hunb a haB haH _
  exact exists_isLoxodromic_mul_of_notMem_fam D hemb.hyperbolic hunb haB haH

/-- **Dahmani--Guirardel--Osin's Corollary 6.12 is a theorem of this
development.**  It is no longer a citation, and `DGOTheorem611` --- which is in
any case false as printed, its `a` not being required to lie outside `H_λ` --- is
no longer a debt of `OsinTheorem12`. -/
theorem dgoCorollary612 : DGOCorollary612.{u} := by
  intro G _ D hemb hnd
  exact exists_isLoxodromic_of_isHyperbolicallyEmbedded D hemb hnd

/-- **`OsinTheorem12` costs two citations.**  `DGOTheorem68` and
`OsinTheorem54` remain; `DGOCorollary612` and `DGOTheorem614` do not. -/
theorem osinTheorem12_of_two (h68 : DGOTheorem68.{u, v}) (h54 : OsinTheorem54.{u}) :
    OsinTheorem12.{u, v} :=
  osinTheorem12_of_612 h68 h54 dgoCorollary612

end GGT
end GroupApproximation
