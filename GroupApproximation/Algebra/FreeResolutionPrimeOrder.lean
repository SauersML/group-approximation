import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# A two-dimensional free resolution leaves no element of prime order

Let `G` be a group and suppose the trivial module `ℤ` has a free resolution of
length two over `ℤG`:

`0 → F₂ → F₁ → F₀ → ℤ → 0`.

Then `G` has no element of prime order, hence it is torsion-free
(`isPowerTorsionFree_of_resolution`).  This is the algebraic half of
Huebschmann's theorem that an aspherical presentation without proper-power
relators presents a torsion-free group: the relation module of such a
presentation is free, and the Fox complex is the resolution above.

The free modules are written concretely, as finitely supported integer functions
on `ι × G` with `g` translating the group coordinate (`FreeZG`, `act`).  For an
element `g` of prime order `p` the proof uses only two explicit facts about a
free module `F` and the norm `N = 1 + g + ⋯ + g^(p-1)`:

* a `g`-fixed element of `F` is a norm (`exists_normMap_eq_of_act_eq`), and
* an element killed by the norm is `g f' - f'` (`exists_act_sub_eq_of_normMap_eq_zero`).

A lift `f` of `1 ∈ ℤ` gives `ξ = g f - f` in the kernel `K` of the augmentation
with `N ξ = 0`.  Pulling `ξ` back through `F₁` and using the two facts on `F₂`
and `F₁` shows `ξ = g k - k` with `k ∈ K`; then `f - k` is fixed, hence a norm,
and the augmentation of a norm is divisible by `p` while `ε (f - k) = 1`.
No group cohomology machinery is used.
-/

namespace GroupApproximation.FreeResolutionPrimeOrder

open Finset

universe u v

section FreeModule

variable {G : Type u} [Group G] {ι : Type v}

/-- The free `ℤG`-module on `ι`: finitely supported integer functions on `ι × G`. -/
abbrev FreeZG (G : Type u) (ι : Type v) := ι × G →₀ ℤ

/-- Left translation of the group coordinate. -/
def shiftEquiv (g : G) : ι × G ≃ ι × G where
  toFun q := (q.1, g * q.2)
  invFun q := (q.1, g⁻¹ * q.2)
  left_inv q := by simp
  right_inv q := by simp

/-- The action of a group element on the free module. -/
noncomputable def act (g : G) : FreeZG G ι →+ FreeZG G ι :=
  (Finsupp.domCongr (shiftEquiv g)).toAddMonoidHom

theorem act_apply (g : G) (f : FreeZG G ι) (i : ι) (h : G) :
    act g f (i, h) = f (i, g⁻¹ * h) :=
  Finsupp.equivMapDomain_apply (shiftEquiv g) f (i, h)

theorem act_act (g g' : G) (f : FreeZG G ι) : act g (act g' f) = act (g * g') f := by
  ext ⟨i, h⟩
  simp only [act_apply, mul_inv_rev, mul_assoc]

theorem act_one (f : FreeZG G ι) : act (1 : G) f = f := by
  ext ⟨i, h⟩
  simp only [act_apply, inv_one, one_mul]

/-- The norm `1 + g + ⋯ + g^(p-1)`. -/
noncomputable def normMap (g : G) (p : ℕ) (f : FreeZG G ι) : FreeZG G ι :=
  ∑ k ∈ range p, act (g ^ k) f

theorem normMap_apply (g : G) (p : ℕ) (f : FreeZG G ι) (i : ι) (h : G) :
    normMap g p f (i, h) = ∑ k ∈ range p, f (i, (g ^ k)⁻¹ * h) := by
  simp only [normMap, Finsupp.finsetSum_apply, act_apply]

theorem normMap_sub (g : G) (p : ℕ) (f f' : FreeZG G ι) :
    normMap g p (f - f') = normMap g p f - normMap g p f' := by
  simp only [normMap, map_sub, Finset.sum_sub_distrib]

theorem normMap_act (g : G) (p : ℕ) (f : FreeZG G ι) :
    normMap g p (act g f) = act g (normMap g p f) := by
  simp only [normMap, map_sum, act_act, pow_mul_comm']

/-- The norm is fixed by `g` when `g ^ p = 1`. -/
theorem act_normMap (g : G) {p : ℕ} (hgp : g ^ p = 1) (f : FreeZG G ι) :
    act g (normMap g p f) = normMap g p f := by
  have h1 : act g (normMap g p f) = ∑ k ∈ range p, act (g ^ (k + 1)) f := by
    simp only [normMap, map_sum, act_act, pow_succ']
  have h2 := Finset.sum_range_succ' (fun k => act (g ^ k) f) p
  have h3 := Finset.sum_range_succ (fun k => act (g ^ k) f) p
  simp only [hgp, pow_zero] at h2 h3
  rw [h1, normMap]
  exact add_right_cancel (h2.symm.trans h3)

/-- Equivariant additive maps commute with the norm. -/
theorem map_normMap {ι' : Type v} (d : FreeZG G ι →+ FreeZG G ι')
    (hd : ∀ (g : G) (f : FreeZG G ι), d (act g f) = act g (d f)) (g : G) (p : ℕ)
    (f : FreeZG G ι) : d (normMap g p f) = normMap g p (d f) := by
  simp only [normMap, map_sum, hd]

/-- An invariant augmentation multiplies a norm by `p`. -/
theorem eps_normMap (eps : FreeZG G ι →+ ℤ)
    (heps : ∀ (g : G) (f : FreeZG G ι), eps (act g f) = eps f) (g : G) (p : ℕ)
    (f : FreeZG G ι) : eps (normMap g p f) = p * eps f := by
  simp only [normMap, map_sum, heps, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end FreeModule

/-! ## Orbits of left multiplication by a periodic element -/

section Orbits

variable {G : Type u} [Group G]

theorem pow_mod_of_pow_eq_one {g : G} {p : ℕ} (hgp : g ^ p = 1) (n : ℕ) :
    g ^ (n % p) = g ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hgp, one_pow, one_mul]

/-- `h ~ h'` when `h = g^k h'` for some `k < p`. -/
def cycleSetoid (g : G) (p : ℕ) (hp : 0 < p) (hgp : g ^ p = 1) : Setoid G where
  r h h' := ∃ k < p, g ^ k * h' = h
  iseqv := by
    refine ⟨fun h => ⟨0, hp, by simp⟩, ?_, ?_⟩
    · rintro h h' ⟨k, hk, rfl⟩
      refine ⟨(p - k) % p, Nat.mod_lt _ hp, ?_⟩
      rw [pow_mod_of_pow_eq_one hgp, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk.le, hgp,
        one_mul]
    · rintro h h' h'' ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
      refine ⟨(k + l) % p, Nat.mod_lt _ hp, ?_⟩
      rw [pow_mod_of_pow_eq_one hgp, pow_add, mul_assoc]

variable (g : G) (p : ℕ) (hp : 0 < p) (hgp : g ^ p = 1)

/-- A chosen representative of the class of `h`. -/
noncomputable def rep (h : G) : G :=
  Quotient.out (Quotient.mk (cycleSetoid g p hp hgp) h)

theorem rep_rel (h : G) : ∃ k < p, g ^ k * rep g p hp hgp h = h := by
  have hq : Quotient.mk (cycleSetoid g p hp hgp) h =
      Quotient.mk (cycleSetoid g p hp hgp) (rep g p hp hgp h) := (Quotient.out_eq _).symm
  exact Quotient.exact hq

theorem rel_rep (h : G) : ∃ k < p, g ^ k * h = rep g p hp hgp h := by
  have hq : Quotient.mk (cycleSetoid g p hp hgp) (rep g p hp hgp h) =
      Quotient.mk (cycleSetoid g p hp hgp) h := Quotient.out_eq _
  exact Quotient.exact hq

theorem rep_eq_of_rel {h h' : G} (hr : ∃ k < p, g ^ k * h' = h) :
    rep g p hp hgp h = rep g p hp hgp h' := by
  unfold rep
  exact congrArg Quotient.out (Quotient.sound (s := cycleSetoid g p hp hgp) hr)

theorem rep_inv_mul (h : G) : rep g p hp hgp (g⁻¹ * h) = rep g p hp hgp h := by
  apply rep_eq_of_rel
  refine ⟨p - 1, by omega, ?_⟩
  have hinv : g ^ (p - 1) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (show 1 ≤ p by omega), hgp]
  rw [hinv]

theorem rep_pow_inv_mul (k : ℕ) (h : G) :
    rep g p hp hgp ((g ^ k)⁻¹ * h) = rep g p hp hgp h := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_inv_rev, mul_assoc, rep_inv_mul, ih]

/-- The exponent reaching an element from a representative is unique below the order. -/
theorem pow_eq_of_pow_mul_eq (hord : orderOf g = p) {j j' : ℕ} (hj : j < p) (hj' : j' < p)
    {x h : G} (h1 : g ^ j * x = h) (h2 : g ^ j' * x = h) : j = j' := by
  have hpow : g ^ j = g ^ j' := mul_right_cancel (h1.trans h2.symm)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hdiff : g ^ (j' - j) = 1 := by
      have h3 : g ^ j * g ^ (j' - j) = g ^ j * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le, hpow]
      exact mul_left_cancel h3
    have hdvd := orderOf_dvd_of_pow_eq_one hdiff
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hdiff : g ^ (j - j') = 1 := by
      have h3 : g ^ j' * g ^ (j - j') = g ^ j' * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le, hpow]
      exact mul_left_cancel h3
    have hdvd := orderOf_dvd_of_pow_eq_one hdiff
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

end Orbits

/-! ## The two facts about free modules -/

section FreeFacts

variable {G : Type u} [Group G] {ι : Type v} (g : G) (p : ℕ) (hp : 0 < p) (hgp : g ^ p = 1)

include hp hgp in
/-- **A `g`-fixed element of a free module is a norm.** -/
theorem exists_normMap_eq_of_act_eq (hord : orderOf g = p) (f : FreeZG G ι)
    (hf : act g f = f) : ∃ f' : FreeZG G ι, normMap g p f' = f := by
  classical
  have hinv : ∀ (k : ℕ) (i : ι) (h : G), f (i, (g ^ k)⁻¹ * h) = f (i, h) := by
    intro k i h
    induction k generalizing h with
    | zero => simp
    | succ k ih =>
        have h1 : ∀ x : G, f (i, g⁻¹ * x) = f (i, x) := fun x => by
          rw [← act_apply g f i x, hf]
        rw [pow_succ, mul_inv_rev, mul_assoc, h1, ih]
  refine ⟨f.filter (fun q => rep g p hp hgp q.2 = q.2), ?_⟩
  ext ⟨i, h⟩
  rw [normMap_apply]
  obtain ⟨j, hj, hjh⟩ := rep_rel g p hp hgp h
  have hr : (g ^ j)⁻¹ * h = rep g p hp hgp h := inv_mul_eq_iff_eq_mul.mpr hjh.symm
  rw [Finset.sum_eq_single j]
  · simp only [Finsupp.filter_apply]
    rw [rep_pow_inv_mul, if_pos hr.symm, hinv]
  · intro k hk hkj
    simp only [Finsupp.filter_apply]
    rw [rep_pow_inv_mul, if_neg]
    intro hk'
    have h2 : g ^ k * rep g p hp hgp h = h := by rw [hk', mul_inv_cancel_left]
    exact hkj (pow_eq_of_pow_mul_eq g p hord (Finset.mem_range.mp hk) hj h2 hjh)
  · intro hj'
    exact absurd (Finset.mem_range.mpr hj) hj'

include hp hgp in
/-- **An element of a free module killed by the norm is `g f' - f'`.** -/
theorem exists_act_sub_eq_of_normMap_eq_zero (hord : orderOf g = p) (f : FreeZG G ι)
    (hf : normMap g p f = 0) : ∃ f' : FreeZG G ι, act g f' - f' = f := by
  classical
  choose e he using rel_rep g p hp hgp
  have hsupp : ∀ q : ι × G,
      (∑ k ∈ range (e q.2), f (q.1, (g ^ k)⁻¹ * rep g p hp hgp q.2)) ≠ 0 →
        q ∈ f.support.biUnion (fun q' => (range p).image (fun m => (q'.1, g ^ m * q'.2))) := by
    rintro ⟨i, h⟩ hq
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have hke : k < e h := Finset.mem_range.mp hk
    have hep : e h < p := (he h).1
    rw [Finset.mem_biUnion]
    refine ⟨(i, (g ^ k)⁻¹ * rep g p hp hgp h), Finsupp.mem_support_iff.mpr hkne, ?_⟩
    rw [Finset.mem_image]
    refine ⟨p - (e h - k), Finset.mem_range.mpr (by omega), ?_⟩
    show (i, g ^ (p - (e h - k)) * ((g ^ k)⁻¹ * rep g p hp hgp h)) = (i, h)
    have h3 : (g ^ k)⁻¹ * rep g p hp hgp h = g ^ (e h - k) * h := by
      rw [inv_mul_eq_iff_eq_mul, ← (he h).2, ← mul_assoc, ← pow_add,
        Nat.add_sub_cancel' hke.le]
    rw [h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (show e h - k ≤ p by omega), hgp,
      one_mul]
  refine ⟨Finsupp.onFinset _ (fun q : ι × G =>
    ∑ k ∈ range (e q.2), f (q.1, (g ^ k)⁻¹ * rep g p hp hgp q.2)) hsupp, ?_⟩
  ext ⟨i, h⟩
  rw [Finsupp.sub_apply, act_apply, Finsupp.onFinset_apply, Finsupp.onFinset_apply]
  show (∑ k ∈ range (e (g⁻¹ * h)), f (i, (g ^ k)⁻¹ * rep g p hp hgp (g⁻¹ * h))) -
      ∑ k ∈ range (e h), f (i, (g ^ k)⁻¹ * rep g p hp hgp h) = f (i, h)
  rw [rep_inv_mul]
  have hA : g ^ (e h + 1) * (g⁻¹ * h) = rep g p hp hgp h := by
    rw [pow_succ, mul_assoc, mul_inv_cancel_left, (he h).2]
  have hB : g ^ e (g⁻¹ * h) * (g⁻¹ * h) = rep g p hp hgp h := by
    rw [(he (g⁻¹ * h)).2, rep_inv_mul]
  have hterm : f (i, (g ^ e h)⁻¹ * rep g p hp hgp h) = f (i, h) := by
    rw [inv_mul_eq_iff_eq_mul.mpr (he h).2.symm]
  by_cases hlast : e h + 1 < p
  · have heq : e (g⁻¹ * h) = e h + 1 :=
      pow_eq_of_pow_mul_eq g p hord (he (g⁻¹ * h)).1 hlast hB hA
    rw [heq, Finset.sum_range_succ, hterm, add_sub_cancel_left]
  · have hp1 : e h + 1 = p := by have := (he h).1; omega
    have hzero : g ^ 0 * (g⁻¹ * h) = rep g p hp hgp h := by
      rw [← hA, hp1, hgp, pow_zero]
    have heq : e (g⁻¹ * h) = 0 :=
      pow_eq_of_pow_mul_eq g p hord (he (g⁻¹ * h)).1 hp hB hzero
    have hsum : ∑ k ∈ range (e h + 1), f (i, (g ^ k)⁻¹ * rep g p hp hgp h) = 0 := by
      rw [hp1, ← normMap_apply, hf, Finsupp.zero_apply]
    rw [Finset.sum_range_succ, hterm] at hsum
    rw [heq, Finset.sum_range_zero]
    omega

end FreeFacts

/-! ## The resolution -/

/-- A free resolution `0 → F₂ → F₁ → F₀ → ℤ → 0` of the trivial module over `ℤG`. -/
structure LengthTwoFreeResolution (G : Type u) [Group G] (ι₀ ι₁ ι₂ : Type v) where
  d₁ : FreeZG G ι₁ →+ FreeZG G ι₀
  d₂ : FreeZG G ι₂ →+ FreeZG G ι₁
  eps : FreeZG G ι₀ →+ ℤ
  d₁_act : ∀ (g : G) (f : FreeZG G ι₁), d₁ (act g f) = act g (d₁ f)
  d₂_act : ∀ (g : G) (f : FreeZG G ι₂), d₂ (act g f) = act g (d₂ f)
  eps_act : ∀ (g : G) (f : FreeZG G ι₀), eps (act g f) = eps f
  eps_surjective : Function.Surjective eps
  exact₀ : ∀ y, eps y = 0 → ∃ z, d₁ z = y
  exact₁ : ∀ y, d₁ y = 0 → ∃ z, d₂ z = y
  comp₁ : ∀ z, d₁ (d₂ z) = 0
  comp₀ : ∀ z, eps (d₁ z) = 0
  d₂_injective : Function.Injective d₂

variable {G : Type u} [Group G] {ι₀ ι₁ ι₂ : Type v}

/-- **No element of prime order.** -/
theorem eq_one_of_pow_prime_eq_one (R : LengthTwoFreeResolution G ι₀ ι₁ ι₂)
    {p : ℕ} (hp : p.Prime) {g : G} (hgp : g ^ p = 1) : g = 1 := by
  by_contra hg1
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hp0 : 0 < p := hp.pos
  obtain ⟨f, hf⟩ := R.eps_surjective 1
  have hξ : R.eps (act g f - f) = 0 := by rw [map_sub, R.eps_act, sub_self]
  obtain ⟨y, hy⟩ := R.exact₀ _ hξ
  have hNξ : normMap g p (act g f - f) = 0 := by
    rw [normMap_sub, normMap_act, act_normMap g hgp, sub_self]
  have hNy : R.d₁ (normMap g p y) = 0 := by
    rw [map_normMap R.d₁ R.d₁_act, hy, hNξ]
  obtain ⟨z, hz⟩ := R.exact₁ _ hNy
  have hzfix : act g z = z := by
    apply R.d₂_injective
    rw [R.d₂_act, hz, act_normMap g hgp]
  obtain ⟨z', hz'⟩ := exists_normMap_eq_of_act_eq g p hp0 hgp hord z hzfix
  have hN0 : normMap g p (y - R.d₂ z') = 0 := by
    rw [normMap_sub, ← map_normMap R.d₂ R.d₂_act, hz', hz, sub_self]
  obtain ⟨y', hy'⟩ := exists_act_sub_eq_of_normMap_eq_zero g p hp0 hgp hord _ hN0
  have hξ' : act g f - f = act g (R.d₁ y') - R.d₁ y' := by
    have h1 : y = (act g y' - y') + R.d₂ z' := by rw [hy', sub_add_cancel]
    rw [← hy, h1, map_add, R.comp₁, add_zero, map_sub, R.d₁_act]
  have hfix0 : act g (f - R.d₁ y') = f - R.d₁ y' := by
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hξ'
  obtain ⟨u, hu⟩ := exists_normMap_eq_of_act_eq g p hp0 hgp hord _ hfix0
  have h1 : R.eps (f - R.d₁ y') = 1 := by rw [map_sub, hf, R.comp₀, sub_zero]
  have h2 : R.eps (normMap g p u) = p * R.eps u := eps_normMap R.eps R.eps_act g p u
  rw [hu, h1] at h2
  have hdvd : (p : ℤ) ∣ 1 := ⟨R.eps u, h2⟩
  have hp1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by omega) hdvd
  have := hp.two_le
  omega

/-- **A group with a length-two free resolution of `ℤ` is torsion-free.** -/
theorem isPowerTorsionFree_of_resolution (R : LengthTwoFreeResolution G ι₀ ι₁ ι₂) :
    IsPowerTorsionFree G := by
  intro g n hn hgn
  by_contra hg1
  have hord_pos : 0 < orderOf g :=
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hgn) hn
  have hord1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  have hq : (orderOf g).minFac.Prime := Nat.minFac_prime hord1
  obtain ⟨c, hc⟩ := Nat.minFac_dvd (orderOf g)
  have hx : (g ^ c) ^ (orderOf g).minFac = 1 := by
    rw [← pow_mul, mul_comm, ← hc, pow_orderOf_eq_one]
  have hgc : g ^ c = 1 := eq_one_of_pow_prime_eq_one R hq hx
  have hdvd2 : orderOf g ∣ c := orderOf_dvd_of_pow_eq_one hgc
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc
      omega
    · exact h0
  have hclt : c < orderOf g := by
    have h2c := Nat.mul_le_mul_right c hq.two_le
    omega
  have := Nat.le_of_dvd hcpos hdvd2
  omega

end GroupApproximation.FreeResolutionPrimeOrder

#audit_axioms GroupApproximation.FreeResolutionPrimeOrder.act_normMap
#audit_axioms GroupApproximation.FreeResolutionPrimeOrder.exists_normMap_eq_of_act_eq
#audit_axioms GroupApproximation.FreeResolutionPrimeOrder.exists_act_sub_eq_of_normMap_eq_zero
#audit_axioms GroupApproximation.FreeResolutionPrimeOrder.eq_one_of_pow_prime_eq_one
#audit_axioms GroupApproximation.FreeResolutionPrimeOrder.isPowerTorsionFree_of_resolution
