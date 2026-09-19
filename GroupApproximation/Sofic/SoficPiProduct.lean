import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.SoficTransfer
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.MeanInequalities

/-!
# Section 29.3: finite products of sofic groups are sofic

A finite product of sofic groups acts coordinatewise on the product of the
coordinate models.  The whole estimate rests on one exact identity: for
coordinatewise permutations the *agreement* proportion of the product is the
product of the coordinate agreement proportions,

`1 - d(Πp, Πq) = ∏ b, (1 - d(p b, q b))`.

Separation then follows because a product of numbers in `[0,1]` is at most any
one factor, and multiplicativity follows from Bernoulli's inequality
`(1 - δ)^n ≥ 1 - nδ`.  Choosing the coordinate tolerance `δ = min ε 1 / (n+1)`
makes both conclusions hold at tolerance `ε`.

The index type is required to live in `Type` because `FiniteModel` carries a
`Type`-valued coordinate set; the groups themselves are arbitrary.
-/

namespace GroupApproximation

namespace PiSofic

universe u

variable {B : Type} [Fintype B] [DecidableEq B]

/-- The product of finitely many finite models. -/
@[reducible] def piModel (A : B → FiniteModel) : FiniteModel where
  carrier := ∀ b, (A b).carrier
  fintype := inferInstance
  decidableEq := inferInstance

/-- Coordinatewise permutation of a product of finite models. -/
def piPerm {A : B → FiniteModel} (p : ∀ b, Equiv.Perm (A b)) :
    Equiv.Perm (piModel A) :=
  Equiv.piCongrRight p

@[simp] theorem piPerm_apply {A : B → FiniteModel} (p : ∀ b, Equiv.Perm (A b))
    (a : piModel A) (b : B) : piPerm p a b = p b (a b) := rfl

theorem piPerm_mul {A : B → FiniteModel} (p q : ∀ b, Equiv.Perm (A b)) :
    piPerm (fun b => p b * q b) = piPerm p * piPerm q := by
  refine Equiv.ext fun a => ?_
  funext b
  rfl

theorem piPerm_one {A : B → FiniteModel} :
    piPerm (fun b => (1 : Equiv.Perm (A b))) = 1 := by
  refine Equiv.ext fun a => ?_
  funext b
  rfl

/-! ## The agreement proportion -/

/-- The complementary form of the normalized Hamming distance: one minus the
distance is the proportion of points where the permutations agree. -/
theorem one_sub_hammingDistance_eq (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (p q : Equiv.Perm Y) :
    1 - hammingDistance Y p q
      = ((Finset.univ.filter fun y => p y = q y).card : ℝ) / Fintype.card Y := by
  classical
  have hN : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  have hsplit : (Finset.univ.filter fun y : Y => p y = q y).card
      + (Finset.univ.filter fun y : Y => ¬ (p y = q y)).card
      = Fintype.card Y := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hsplitR : ((Finset.univ.filter fun y : Y => p y = q y).card : ℝ)
      + ((Finset.univ.filter fun y : Y => ¬ (p y = q y)).card : ℝ)
      = (Fintype.card Y : ℝ) := by exact_mod_cast hsplit
  rw [hammingDistance, hammingDisagreement, eq_div_iff hN, sub_mul, one_mul,
    div_mul_cancel₀ _ hN]
  simp only [ne_eq] at hsplitR ⊢
  linarith

/-- **The product identity.**  Agreement proportions multiply across
coordinates. -/
theorem one_sub_hammingDistance_piPerm (A : B → FiniteModel)
    (hA : ∀ b, 0 < Fintype.card (A b)) (p q : ∀ b, Equiv.Perm (A b)) :
    1 - hammingDistance (piModel A) (piPerm p) (piPerm q)
      = ∏ b, (1 - hammingDistance (A b) (p b) (q b)) := by
  classical
  have hcard : (Fintype.card (piModel A) : ℝ)
      = ∏ b, (Fintype.card (A b) : ℝ) := by
    have : Fintype.card (piModel A) = ∏ b, Fintype.card (A b) :=
      Fintype.card_pi
    rw [this, Nat.cast_prod]
  have hpos : 0 < Fintype.card (piModel A) := by
    have : Fintype.card (piModel A) = ∏ b, Fintype.card (A b) :=
      Fintype.card_pi
    rw [this]
    exact Finset.prod_pos fun b _ => hA b
  have hfilter : (Finset.univ.filter
        fun a : piModel A => piPerm p a = piPerm q a)
      = Fintype.piFinset (fun b => Finset.univ.filter fun x => p b x = q b x) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    constructor
    · intro hEq b
      exact congrFun hEq b
    · intro hb
      funext b
      exact hb b
  rw [one_sub_hammingDistance_eq _ hpos, hfilter, Fintype.card_piFinset,
    Nat.cast_prod, hcard, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  exact (one_sub_hammingDistance_eq (A b) (hA b) (p b) (q b)).symm

/-! ## Soficity of a finite product -/

variable {K : B → Type u} [∀ b, Group (K b)]

/-- **Section 29.3.**  A product of finitely many sofic groups is sofic. -/
theorem isSofic_pi (h : ∀ b, IsSofic (K b)) : IsSofic (∀ b, K b) := by
  classical
  intro F ε hε
  set n : ℝ := (Fintype.card B : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set δ : ℝ := min ε 1 / (n + 1) with hδdef
  have hmin0 : 0 < min ε 1 := lt_min hε one_pos
  have hδpos : 0 < δ := div_pos hmin0 (by linarith)
  have hδle1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by linarith)]
    have := min_le_right ε 1
    linarith
  have hδle : δ ≤ ε := le_trans (by
    rw [hδdef, div_le_iff₀ (by linarith)]
    nlinarith [hmin0.le]) (min_le_left ε 1)
  have hnδ : n * δ ≤ ε := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [min_le_left ε 1, hmin0.le, hε.le]
  -- coordinate models
  obtain ⟨M⟩ : Nonempty (∀ b, SoficModel (K b) (F.image fun k => k b) δ) := by
    refine ⟨fun b => (h b (F.image fun k => k b) δ hδpos).some⟩
  set A : B → FiniteModel := fun b => (M b).carrier with hA
  have hApos : ∀ b, 0 < Fintype.card (A b) := fun b => (M b).nonempty
  refine ⟨{
    carrier := piModel A
    nonempty := ?_
    map := fun k => piPerm (fun b => (M b).map (k b))
    multiplicative := ?_
    separated := ?_ }⟩
  · have : Fintype.card (piModel A) = ∏ b, Fintype.card (A b) := Fintype.card_pi
    rw [this]
    exact Finset.prod_pos fun b _ => hApos b
  · -- multiplicativity: Bernoulli across the coordinates
    intro g hg k hk
    have hmulperm : (fun b => (M b).map (g b * k b))
        = fun b => (M b).map ((g * k) b) := rfl
    have hsplit : piPerm (fun b => (M b).map (g b)) * piPerm (fun b => (M b).map (k b))
        = piPerm (fun b => (M b).map (g b) * (M b).map (k b)) :=
      (piPerm_mul _ _).symm
    rw [← hmulperm, hsplit]
    have hprod := one_sub_hammingDistance_piPerm A hApos
      (fun b => (M b).map (g b * k b))
      (fun b => (M b).map (g b) * (M b).map (k b))
    have hcoord : ∀ b, 1 - δ ≤
        1 - hammingDistance (A b) ((M b).map (g b * k b))
          ((M b).map (g b) * (M b).map (k b)) := by
      intro b
      have := (M b).multiplicative (g b) (Finset.mem_image_of_mem _ hg)
        (k b) (Finset.mem_image_of_mem _ hk)
      linarith
    have hpow : (1 - δ) ^ Fintype.card B
        ≤ ∏ b, (1 - hammingDistance (A b) ((M b).map (g b * k b))
            ((M b).map (g b) * (M b).map (k b))) := by
      calc (1 - δ) ^ Fintype.card B = ∏ _b : B, (1 - δ) := by
            rw [Finset.prod_const, Finset.card_univ]
        _ ≤ _ := Finset.prod_le_prod (fun b _ => by linarith) (fun b _ => hcoord b)
    have hbern : 1 - n * δ ≤ (1 - δ) ^ Fintype.card B := by
      have := one_add_mul_le_pow (a := -δ) (by linarith) (Fintype.card B)
      rw [hn]
      calc 1 - (Fintype.card B : ℝ) * δ
          = 1 + (Fintype.card B : ℝ) * (-δ) := by ring
        _ ≤ (1 + -δ) ^ Fintype.card B := this
        _ = (1 - δ) ^ Fintype.card B := by ring_nf
    linarith
  · -- separation: one bad coordinate suffices
    intro g hg k hk hne
    obtain ⟨b₀, hb₀⟩ : ∃ b, g b ≠ k b := Function.ne_iff.mp hne
    have hprod := one_sub_hammingDistance_piPerm A hApos
      (fun b => (M b).map (g b)) (fun b => (M b).map (k b))
    have hbound : ∏ b, (1 - hammingDistance (A b) ((M b).map (g b))
        ((M b).map (k b))) ≤ δ := by
      have hfac : ∀ b, 0 ≤ 1 - hammingDistance (A b) ((M b).map (g b))
          ((M b).map (k b)) := by
        intro b
        have := hammingDistance_le_one (A b) ((M b).map (g b)) ((M b).map (k b))
        linarith
      have hle1 : ∀ b, 1 - hammingDistance (A b) ((M b).map (g b))
          ((M b).map (k b)) ≤ 1 := by
        intro b
        have := hammingDistance_nonnegative (A b) ((M b).map (g b))
          ((M b).map (k b))
        linarith
      have hsep := (M b₀).separated (g b₀) (Finset.mem_image_of_mem _ hg)
        (k b₀) (Finset.mem_image_of_mem _ hk) hb₀
      have hsplit := Finset.mul_prod_erase (Finset.univ : Finset B)
        (fun b => 1 - hammingDistance (A b) ((M b).map (g b)) ((M b).map (k b)))
        (Finset.mem_univ b₀)
      rw [← hsplit]
      have hrest : ∏ b ∈ (Finset.univ : Finset B).erase b₀,
          (1 - hammingDistance (A b) ((M b).map (g b)) ((M b).map (k b))) ≤ 1 :=
        Finset.prod_le_one (fun b _ => hfac b) (fun b _ => hle1 b)
      have hb₀le : 1 - hammingDistance (A b₀) ((M b₀).map (g b₀))
          ((M b₀).map (k b₀)) ≤ δ := by linarith
      nlinarith [hfac b₀, Finset.prod_nonneg
        (fun b (_ : b ∈ (Finset.univ : Finset B).erase b₀) => hfac b)]
    linarith
/-- A two-factor product, packaged as a dependent product over `Bool`. -/
def piBoolMulEquiv (K : Bool → Type u) [∀ b, Group (K b)] :
    (∀ b, K b) ≃* K true × K false where
  toFun f := (f true, f false)
  invFun p := fun b => Bool.rec p.2 p.1 b
  left_inv f := by
    funext b
    cases b <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl

/-- **Section 29.3, binary case.**  A product of two sofic groups is sofic. -/
theorem isSofic_prod {G H : Type u} [Group G] [Group H]
    (hG : IsSofic G) (hH : IsSofic H) : IsSofic (G × H) := by
  classical
  letI : ∀ b : Bool, Group (cond b G H) := fun b =>
    Bool.rec (motive := fun b => Group (cond b G H)) ‹Group H› ‹Group G› b
  have hK : ∀ b : Bool, IsSofic (cond b G H) := by
    intro b
    cases b
    · exact hH
    · exact hG
  have hpi : IsSofic (∀ b : Bool, cond b G H) := isSofic_pi hK
  exact (isSofic_mulEquiv_iff (piBoolMulEquiv (fun b => cond b G H))).mp hpi

end PiSofic

end GroupApproximation
