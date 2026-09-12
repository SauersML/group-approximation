import GroupApproximation.CharClass.CupOneCoboundary
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# Signed graded commutativity of the cup product over an arbitrary commutative ring

`SteenrodCupOne.cup_comm` proves `a ⌣ b = cohCast _ (b ⌣ a)` at `ZMod 2`, unsigned and
in all degrees, from the cup-1 coboundary formula.  Over a ring in which `1 ≠ -1` the
same descent gives the signed statement

```text
a ⌣ b = (-1) ^ (p * q) • cohCast (Nat.add_comm q p) (b ⌣ a),
```

and its corollary `cup_comm_of_even`, which is the only commutativity the LIX program
consumes: Chern classes have even degree, so every commutation the even side performs
is sign-free.

The descent is the `ZMod 2` one with two changes.  The coboundary of the cup-1 is a
*scaled* sum of the two low terms, so the cocycle class must be additive **and**
homogeneous (`CupOneLocal.cocycleClassK_add`, `.cocycleClassK_smul`); and the conclusion is
read off by multiplying by `(-1)^n` rather than by `x + y = 0 → x = y`.  The degenerate bidegree
`(0,0)`, where the cup-1 has no room, is the same argument as at `ZMod 2`: the only
`1`-cut of a `0`-simplex uses the whole vertex set for both families, so the cup product
is literally a product in `K` (`cochainCupI_zero_zero_comm_of`).
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. The cocycle class is linear

**These four are `sp-coeff`'s, not this lane's**, and they are parked in a lane-local
namespace so that pulling them into `CoeffCohomology.lean` cannot collide with the copies
here.  `CharClass` was frozen for a landing when this lane needed them; `sp-coeff` has
claimed the first three and will add them to the base layer immediately after, at which
point this whole section is deleted and the four call sites below point at theirs.  They
are namespaced rather than `private` so that a grep for them still finds them. -/

namespace CupOneLocal

/-- **`cocycleClassK` is additive.**  The generic twin of `SteenrodCupOne.cocycleClass_add`,
proved the same way: `iCycles` is a mono, so injective. -/
theorem cocycleClassK_add (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup K X n)
    (hφ : cochainCoboundary K X n φ = 0) (hψ : cochainCoboundary K X n ψ = 0)
    (hφψ : cochainCoboundary K X n (φ + ψ) = 0) :
    cocycleClassK K X n (φ + ψ) hφψ
      = cocycleClassK K X n φ hφ + cocycleClassK K X n ψ hψ := by
  unfold cocycleClassK
  rw [← map_add]
  refine congrArg (fun c => ((cochainCxK K X).homologyπ n).hom c) ?_
  apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles n)).1 inferInstance
  simp only [map_add, iCycles_cyclesMkK]
  rfl

/-- **`cocycleClassK` is homogeneous.** -/
theorem cocycleClassK_smul (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) (s : K)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0)
    (hsφ : cochainCoboundary K X n (s • φ) = 0) :
    cocycleClassK K X n (s • φ) hsφ = s • cocycleClassK K X n φ hφ := by
  unfold cocycleClassK
  rw [← map_smul]
  refine congrArg (fun c => ((cochainCxK K X).homologyπ n).hom c) ?_
  apply (ModuleCat.mono_iff_injective ((cochainCxK K X).iCycles n)).1 inferInstance
  simp only [map_smul, iCycles_cyclesMkK]
  rfl

/-- The coboundary is `K`-linear.  A fourth base-layer fact `sp-coeff` has not claimed;
offered to them. -/
theorem cochainCoboundary_smul {K : Type} [CommRing K] {X : TopCat.{0}} (m : ℕ) (s : K)
    (ξ : singularCochainGroup K X m) :
    cochainCoboundary K X m (s • ξ) = s • cochainCoboundary K X m ξ := by
  unfold cochainCoboundary
  exact map_smul _ _ _

end CupOneLocal

/-! ## 2. Degree casts -/

/-- A cast `cochainCup` is a `cochainCupI 0 · · ·` at the target degree.  The `ZMod 2`
statement is `SteenrodCupOne.cochainCast_cochainCupI_zero`; its proof uses no
characteristic-two step. -/
theorem cochainCast_cochainCupI_zero_of {K : Type} [CommRing K] {X : TopCat.{0}}
    (a b n : ℕ) (h : a + b = n)
    (φ : singularCochainGroup K X a) (ψ : singularCochainGroup K X b) :
    cochainCast h (cochainCup a b φ ψ) = cochainCupI 0 a b n φ ψ := by
  subst h
  rw [cochainCast_rfl]
  exact (cochainCupI_zero a b φ ψ).symm

/-- A degree cast of a cocycle is a cocycle.  Also `sp-coeff`'s, claimed; parked here for
the same reason as §1. -/
theorem CupOneLocal.cochainCoboundary_cochainCast {K : Type} [CommRing K] {X : TopCat.{0}}
    {m m' : ℕ} (h : m = m') (ξ : singularCochainGroup K X m)
    (hξ : cochainCoboundary K X m ξ = 0) :
    cochainCoboundary K X m' (cochainCast h ξ) = 0 := by
  subst h
  rw [cochainCast_rfl]
  exact hξ

/-! ## 3. The coboundary formula on cocycles -/

/-- **The cup-1 coboundary formula for cocycles**, at every literal degree `n`
simultaneously: only the two low terms survive. -/
theorem cochainCupOne_coboundary_cocycle {K : Type} [CommRing K] {X : TopCat.{0}} (p q n : ℕ)
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    cochainCoboundary K X n (cochainCupOne p q n φ ψ)
      = (-1 : K) ^ n • cochainCupI 0 p q (n + 1) φ ψ
        + (-1 : K) ^ (p + q + p * q) • cochainCupI 0 q p (n + 1) ψ φ := by
  rw [cochainCupOne_coboundary, hφ, hψ, cochainCupOne_zero_left, cochainCupOne_zero_right,
    smul_zero, zero_add, zero_add]

/-! ## 4. Graded commutativity -/

/-- **Signed graded commutativity of the cup product over any commutative ring.** -/
theorem cup_comm_signed {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a : Hmod K X p) (b : Hmod K X q) :
    cup a b = (-1 : K) ^ (p * q) • cohCast (Nat.add_comm q p) (cup b a) := by
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · -- Degenerate bidegree: `p = q = 0`, where the cup-1 has no room.
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp
    subst hq
    obtain ⟨φ, hφ, rfl⟩ := exists_cocycleOf a
    obtain ⟨ψ, hψ, rfl⟩ := exists_cocycleOf b
    have hcomm : cochainCup 0 0 φ ψ = cochainCup 0 0 ψ φ := by
      rw [← cochainCupI_zero 0 0 φ ψ, ← cochainCupI_zero 0 0 ψ φ]
      exact cochainCupI_zero_zero_comm_of φ ψ
    have hscalar : (-1 : K) ^ (0 * 0) = 1 := by norm_num
    rw [hscalar, one_smul, cohCast_congr (Nat.add_comm 0 0) rfl, cohCast_rfl, cup_mkOf,
      cup_mkOf]
    exact cocycleClassK_congr K X 0 hcomm _ _
  · -- General bidegree.
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hn' : q + p = n + 1 := (Nat.add_comm q p).trans hn
    obtain ⟨φ, hφ, rfl⟩ := exists_cocycleOf a
    obtain ⟨ψ, hψ, rfl⟩ := exists_cocycleOf b
    have hδμ := cochainCupOne_coboundary_cocycle p q n φ hφ ψ hψ
    have hpq : cochainCoboundary K X (p + q) (cochainCup p q φ ψ) = 0 :=
      cochainCup_respects_cocycles p q φ ψ hφ hψ
    have hqp : cochainCoboundary K X (q + p) (cochainCup q p ψ φ) = 0 :=
      cochainCup_respects_cocycles q p ψ φ hψ hφ
    have e1 : cochainCast hn (cochainCup p q φ ψ) = cochainCupI 0 p q (n + 1) φ ψ :=
      cochainCast_cochainCupI_zero_of p q (n + 1) hn φ ψ
    have e2 : cochainCast hn' (cochainCup q p ψ φ) = cochainCupI 0 q p (n + 1) ψ φ :=
      cochainCast_cochainCupI_zero_of q p (n + 1) hn' ψ φ
    have hcast1 : cochainCoboundary K X (n + 1) (cochainCast hn (cochainCup p q φ ψ)) = 0 :=
      CupOneLocal.cochainCoboundary_cochainCast hn _ hpq
    have hcast2 : cochainCoboundary K X (n + 1) (cochainCast hn' (cochainCup q p ψ φ)) = 0 :=
      CupOneLocal.cochainCoboundary_cochainCast hn' _ hqp
    have h1' : cochainCoboundary K X (n + 1) (cochainCupI 0 p q (n + 1) φ ψ) = 0 := by
      rw [← e1]
      exact hcast1
    have h2' : cochainCoboundary K X (n + 1) (cochainCupI 0 q p (n + 1) ψ φ) = 0 := by
      rw [← e2]
      exact hcast2
    have hs1 : cochainCoboundary K X (n + 1)
        ((-1 : K) ^ n • cochainCupI 0 p q (n + 1) φ ψ) = 0 := by
      rw [CupOneLocal.cochainCoboundary_smul, h1', smul_zero]
    have hs2 : cochainCoboundary K X (n + 1)
        ((-1 : K) ^ (p + q + p * q) • cochainCupI 0 q p (n + 1) ψ φ) = 0 := by
      rw [CupOneLocal.cochainCoboundary_smul, h2', smul_zero]
    have hsum : cochainCoboundary K X (n + 1)
        ((-1 : K) ^ n • cochainCupI 0 p q (n + 1) φ ψ
          + (-1 : K) ^ (p + q + p * q) • cochainCupI 0 q p (n + 1) ψ φ) = 0 := by
      rw [← hδμ]
      exact cochainCoboundary_cochainCoboundaryK K X n (cochainCupOne p q n φ ψ)
    have hzero : cocycleClassK K X (n + 1)
        ((-1 : K) ^ n • cochainCupI 0 p q (n + 1) φ ψ
          + (-1 : K) ^ (p + q + p * q) • cochainCupI 0 q p (n + 1) ψ φ) hsum = 0 := by
      have step1 := cocycleClassK_coboundary_zero K X n (cochainCupOne p q n φ ψ)
        (cochainCoboundary_cochainCoboundaryK K X n (cochainCupOne p q n φ ψ))
      rwa [cocycleClassK_congr K X (n + 1) hδμ
        (cochainCoboundary_cochainCoboundaryK K X n (cochainCupOne p q n φ ψ)) hsum] at step1
    rw [CupOneLocal.cocycleClassK_add K X (n + 1) _ _ hs1 hs2 hsum,
      CupOneLocal.cocycleClassK_smul K X (n + 1) _ _ h1' hs1,
      CupOneLocal.cocycleClassK_smul K X (n + 1) _ _ h2' hs2] at hzero
    have hA : cohCast hn (cup (cocycleClassK K X p φ hφ) (cocycleClassK K X q ψ hψ))
        = cocycleClassK K X (n + 1) (cochainCupI 0 p q (n + 1) φ ψ) h1' := by
      rw [cup_mkOf, cohCast_cocycleClassOf K hn (cochainCup p q φ ψ) hpq hcast1]
      exact cocycleClassK_congr K X (n + 1) e1 hcast1 h1'
    have hB : cohCast hn' (cup (cocycleClassK K X q ψ hψ) (cocycleClassK K X p φ hφ))
        = cocycleClassK K X (n + 1) (cochainCupI 0 q p (n + 1) ψ φ) h2' := by
      rw [cup_mkOf, cohCast_cocycleClassOf K hn' (cochainCup q p ψ φ) hqp hcast2]
      exact cocycleClassK_congr K X (n + 1) e2 hcast2 h2'
    rw [← hA, ← hB] at hzero
    have hsq : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hkey : (-1 : K) ^ n * (-1 : K) ^ (p + q + p * q) = - (-1 : K) ^ (p * q) := by
      rw [← pow_add]
      have hpar : (n + (p + q + p * q)) % 2 = (p * q + 1) % 2 := by omega
      rw [neg_one_pow_congr_mod_two (K := K) hpar, pow_succ]
      ring
    have hstep := congrArg (fun x : Hmod K X (n + 1) => ((-1 : K) ^ n) • x) hzero
    simp only [smul_add, smul_smul, smul_zero, hsq, hkey, one_smul, neg_smul] at hstep
    refine cohCast_injective hn ?_
    rw [cohCast_smul, cohCast_cohCast,
      cohCast_congr ((Nat.add_comm q p).trans hn) hn']
    exact add_neg_eq_zero.1 hstep

/-- **The corollary the program consumes.**  Two classes commute when one of them has
even degree; no sign survives.  Chern classes have even degree, so every commutation the
even side of the LIX program performs is an instance of this. -/
theorem cup_comm_of_even_left {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (hp : Even p) (a : Hmod K X p) (b : Hmod K X q) :
    cup a b = cohCast (Nat.add_comm q p) (cup b a) := by
  have hpq : (p * q) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.even_iff.1 hp, Nat.zero_mul, Nat.zero_mod]
  have h1 : (-1 : K) ^ (p * q) = 1 := by
    rw [neg_one_pow_eq_pow_mod_two, hpq, pow_zero]
  rw [cup_comm_signed, h1, one_smul]

/-- The same with the even degree on the right. -/
theorem cup_comm_of_even_right {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (hq : Even q) (a : Hmod K X p) (b : Hmod K X q) :
    cup a b = cohCast (Nat.add_comm q p) (cup b a) := by
  have hpq : (p * q) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.even_iff.1 hq, Nat.mul_zero, Nat.zero_mod]
  have h1 : (-1 : K) ^ (p * q) = 1 := by
    rw [neg_one_pow_eq_pow_mod_two, hpq, pow_zero]
  rw [cup_comm_signed, h1, one_smul]

end

end CharClass
end GroupApproximation
