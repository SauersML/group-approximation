import GroupApproximation.GGT.ElementaryOsinSNormal

/-!
# The elementary closure is proper, from the centralizer alone

`GGT.ElementaryFillConjugate` reduces
`Manuscript.NonMF.OsinNormalReduction.ExistsIndependentConjugate` to two things:
the axis dichotomy, and

    hproper : ActsNonElementarily ⊤ x → ∀ q, IsLoxodromic q x → NotCommensurated q

where `NotCommensurated q` is `∃ a, ¬ ∃ m n ≠ 0, a qᵐ a⁻¹ = qⁿ` --- that is,
`∃ a, a ∉ elementaryClosure q`.  Nothing in the repository inhabits `hproper`.

`GGT.ElementaryOsinSNormal` proves it from `ElementaryClosureVirtuallyCyclic`
(Osin, Theorem 6.8).  This module proves it from a **weaker** hypothesis, so the
properness step no longer waits on the full virtual-cyclicity theorem:

    NoIndependentPairInCentralizer:
      the centralizer of a loxodromic element contains no two independent
      loxodromic elements.

That is Osin, Corollary 6.9 (the centralizer, indeed the elementary closure, of a
loxodromic element of an acylindrical action is elementary), and it is implied by
Theorem 6.8 but does not imply it.

## The argument

Suppose every `f` lies in `E(q)`, and let `a, b` be the two independent ambient
loxodromics.

* Translation length forces the two exponents in a witness to agree up to sign
  (`natAbs_eq_of_mem_elementaryClosure`), so `a qⁿ¹ a⁻¹ = q^{±n₁}`.  Conjugating
  twice cancels the sign: `a²` commutes with `qⁿ¹`, and likewise `b²` commutes
  with `qⁿ²`.  This is `exists_ne_zero_commute_sq_of_mem_elementaryClosure`, and
  it is the only place the sign refinement is used anywhere.
* Both squares then commute with the single element `u = q^{n₁n₂}`, which is
  loxodromic because `n₁n₂ ≠ 0`.
* `a²` and `b²` are loxodromic, and independent because independence is a bound
  on the Gromov products of two *sets* of orbit points and passing to powers only
  shrinks those sets (`independent_pow`).
* So the centralizer of `u` contains two independent loxodromics.

## The other named fact, at one line

`LoxodromicOfCommute` needs no elementary-closure theory at all once Bowditch's
dichotomy is available: `Sofic/HullSuitabilityGeometry.lean` already proves
`isEscaping_of_commutes_of_not_isOfFinOrder` --- an infinite-order element
commuting with a loxodromic escapes every bounded set, by finiteness of
centralizer balls --- and the dichotomy upgrades escape to loxodromy.  So
`isLoxodromic_of_commute_of_escapingIsLoxodromic` reduces that fact to

    EscapingIsLoxodromic:  every escaping element is loxodromic

which is Bowditch's theorem that an acylindrical action on a hyperbolic space has
no parabolic elements (Osin, Theorem 1.1).  `GGT.ElementaryFillCentralizer`
reduces the same fact to a Morse-stability input (`OrbitFellowTravels`); the two
reductions are independent, and whichever residual is discharged first closes it.

## No imports below the landed layer

`GGT.ElementaryFillConjugate` and `GGT.ElementaryFillCentralizer` are not
imported here, so nothing in the root import list depends on them.  Their
`Commensurates q a` is definitionally `a ∈ elementaryClosure q`, so
`notCommensurated_of_centralizer` below is `NotCommensurated q` and can be
consumed there verbatim.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

section Inputs

/-- **Osin, Corollary 6.9.**  The centralizer of a loxodromic element of an
acylindrical action is elementary, so it contains no two independent loxodromic
elements.  Implied by Theorem 6.8 (`ElementaryClosureVirtuallyCyclic`), and
weaker than it. -/
def NoIndependentPairInCentralizer (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ u a b : G, IsLoxodromic u x → IsLoxodromic a x → IsLoxodromic b x →
    Commute a u → Commute b u → ¬ Independent a b x

/-- **Bowditch's dichotomy** (Osin, Theorem 1.1): an acylindrical action on a
hyperbolic space has no parabolic elements, so an element whose power orbit
escapes every bounded set is loxodromic. -/
def EscapingIsLoxodromic (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ c : G, IsEscaping c x → IsLoxodromic c x

end Inputs

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Independence passes to powers -/

/-- Independence is a bound on the Gromov products of two *sets* of orbit
points, and the orbit of a power is a subset of the orbit.  So it passes to
powers with the same constant, with no hypothesis on the exponents. -/
theorem independent_zpow {a b : G} {x : X} (h : Independent a b x) (k l : ℤ) :
    Independent (a ^ k) (b ^ l) x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n m => ?_⟩
  rw [← zpow_mul, ← zpow_mul]
  exact hC (k * n) (l * m)

/-- The natural-power form. -/
theorem independent_pow {a b : G} {x : X} (h : Independent a b x) (k l : ℕ) :
    Independent (a ^ k) (b ^ l) x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n m => ?_⟩
  rw [← zpow_natCast a k, ← zpow_natCast b l, ← zpow_mul, ← zpow_mul]
  exact hC ((k : ℤ) * n) ((l : ℤ) * m)

/-! ## Squares in the elementary closure centralize a power -/

/-- **The sign cancels on squaring.**  For loxodromic `g`, an element `h` of
`E(g)` satisfies `h gⁿ h⁻¹ = g^{±n}` for some `n ≠ 0`; conjugating twice returns
`gⁿ` in both cases, so `h²` commutes with `gⁿ`.

This is the only consumer of the translation-length normalisation
`natAbs_eq_of_mem_elementaryClosure`, and it is what turns "everything
commensurates the axis of `q`" into "everything squared centralizes one fixed
loxodromic element". -/
theorem exists_ne_zero_commute_sq_of_mem_elementaryClosure
    (hiso : IsIsometricAction G X) {g h : G} {x : X} (hg : IsLoxodromic g x)
    (hh : h ∈ elementaryClosure g) :
    ∃ n : ℤ, n ≠ 0 ∧ Commute (h * h) (g ^ n) := by
  obtain ⟨n, hn, hcase⟩ := conj_zpow_eq_or_of_mem_elementaryClosure hiso hg hh
  refine ⟨n, hn, ?_⟩
  rcases hcase with heq | heq
  · have hcomm : h * g ^ n = g ^ n * h := by
      calc h * g ^ n = h * g ^ n * h⁻¹ * h := by group
        _ = g ^ n * h := by rw [heq]
    have hc : Commute h (g ^ n) := hcomm
    exact hc.mul_left hc
  · have hstep : h * h * g ^ n * (h * h)⁻¹ = g ^ n := by
      have h1 : h * h * g ^ n * (h * h)⁻¹ = h * (h * g ^ n * h⁻¹) * h⁻¹ := by
        group
      rw [h1, heq]
      have h2 : h * g ^ (-n) * h⁻¹ = (h * g ^ n * h⁻¹)⁻¹ := by group
      rw [h2, heq, ← zpow_neg, neg_neg]
    have hcomm : h * h * g ^ n = g ^ n * (h * h) := by
      calc h * h * g ^ n = h * h * g ^ n * (h * h)⁻¹ * (h * h) := by group
        _ = g ^ n * (h * h) := by rw [hstep]
    exact hcomm

/-! ## Properness -/

/-- **The elementary closure of a loxodromic element is a proper subgroup**, for
a non-elementary acylindrical action, from Osin's Corollary 6.9 alone.

If it were everything, the two independent ambient loxodromics `a, b` would both
commensurate the axis of `q`; their squares would then centralize the single
loxodromic element `q^{n₁n₂}`; and `a²`, `b²` are themselves independent
loxodromics. -/
theorem exists_notMem_elementaryClosure_of_centralizer
    (hiso : IsIsometricAction G X) {x : X}
    (hcen : NoIndependentPairInCentralizer G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) {q : G}
    (hq : IsLoxodromic q x) :
    ∃ f : G, f ∉ elementaryClosure q := by
  obtain ⟨a, -, b, -, ha, hb, hab⟩ := hG
  by_contra hall
  push_neg at hall
  obtain ⟨n₁, hn₁, hc₁⟩ :=
    exists_ne_zero_commute_sq_of_mem_elementaryClosure hiso hq (hall a)
  obtain ⟨n₂, hn₂, hc₂⟩ :=
    exists_ne_zero_commute_sq_of_mem_elementaryClosure hiso hq (hall b)
  have hu : IsLoxodromic (q ^ (n₁ * n₂)) x :=
    isLoxodromic_zpow hiso hq (mul_ne_zero hn₁ hn₂)
  have hcu₁ : Commute (a * a) (q ^ (n₁ * n₂)) := by
    have h := hc₁.zpow_right n₂
    rwa [← zpow_mul] at h
  have hcu₂ : Commute (b * b) (q ^ (n₁ * n₂)) := by
    have h := hc₂.zpow_right n₁
    rw [← zpow_mul, mul_comm n₂ n₁] at h
    exact h
  have hasq : IsLoxodromic (a * a) x := by
    have h := isLoxodromic_pow ha (k := 2) (by norm_num)
    rwa [pow_two] at h
  have hbsq : IsLoxodromic (b * b) x := by
    have h := isLoxodromic_pow hb (k := 2) (by norm_num)
    rwa [pow_two] at h
  have hindsq : Independent (a * a) (b * b) x := by
    have h := independent_pow hab 2 2
    rwa [pow_two, pow_two] at h
  exact hcen (q ^ (n₁ * n₂)) (a * a) (b * b) hu hasq hbsq hcu₁ hcu₂ hindsq

/-- The same conclusion in the shape `GGT.ElementaryFill.NotCommensurated q`
takes, so that module's `hproper` can be discharged with this term.  The two
statements are the same proposition: `Commensurates q a` is
`a ∈ elementaryClosure q` unfolded. -/
theorem notCommensurated_of_centralizer (hiso : IsIsometricAction G X) {x : X}
    (hcen : NoIndependentPairInCentralizer G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) (q : G)
    (hq : IsLoxodromic q x) :
    ∃ a : G, ¬ ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ a * q ^ m * a⁻¹ = q ^ n :=
  exists_notMem_elementaryClosure_of_centralizer hiso hcen hG hq

/-! ## The two named facts, from the sharpened inputs -/

/-- **`ExistsIndependentConjugate` from Corollary 6.9 and the common-power
theorem**, with no use of Theorem 6.8. -/
theorem exists_independent_conjugate_of_centralizer
    (hiso : IsIsometricAction G X) {x : X}
    (hindep : IndependentOfNoCommonZpow G x)
    (hcen : NoIndependentPairInCentralizer G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) (q : G)
    (hq : IsLoxodromic q x) :
    ∃ a : G, Independent q (a * q * a⁻¹) x := by
  obtain ⟨f, hf⟩ := exists_notMem_elementaryClosure_of_centralizer hiso hcen hG hq
  exact ⟨f, independent_conj_of_notMem_elementaryClosure hiso hindep hq hf⟩

/-- **`LoxodromicOfCommute` from Bowditch's dichotomy, at one line.**  An
infinite-order element commuting with a loxodromic escapes every bounded set ---
that is `isEscaping_of_commutes_of_not_isOfFinOrder`, proved from finiteness of
centralizer balls --- and the dichotomy makes an escaping element loxodromic. -/
theorem isLoxodromic_of_commute_of_escapingIsLoxodromic
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hbow : EscapingIsLoxodromic G x) (g c : G) (hg : IsLoxodromic g x)
    (hcg : Commute c g) (hfin : ¬ IsOfFinOrder c) : IsLoxodromic c x :=
  hbow c (isEscaping_of_commutes_of_not_isOfFinOrder hiso hacy hg hcg hfin)

/-! ## The exclusion step of Osin's Theorem 1.1

`GGT.WPDAcylindricalHyperbolicity` needs properness of `E(g)` in a form that can
be used *before* non-elementarity is known: its pair comes from
Dahmani--Guirardel--Osin's Theorem 6.14 as free generators, and all that is known
of it is that it has no common nonzero power.  The versions above assume
`ActsNonElementarily ⊤ x` and so cannot establish it.

The pair does not have to arrive loxodromic --- the hypothesis promotes it.  If
everything lay in `E(g)`, then `a²` and `b²` centralize the loxodromic
`u = g^{n₁n₂}`; a common-power-free pair has both entries of infinite order, so
`a²` and `b²` do too, and an infinite-order element commuting with a loxodromic is
loxodromic by Bowditch; freedom from common powers survives squaring, so
`IndependentOfNoCommonZpow` makes them independent.  Corollary 6.9 then applies.

The trade against the route through Theorem 6.8 is two inputs for one, and both
of the two are cheaper: Corollary 6.9 reduces to a single Morse output
(`GGT.ElementaryCentralizerAxis`), Bowditch to the single local estimate
`EscapingBoundedTurn` (`GGT.ElementaryBowditch`), while the finite-index content
of Theorem 6.8 has no route in this development at all. -/

/-- An element of infinite order has a square of infinite order. -/
theorem not_isOfFinOrder_mul_self {c : G} (hc : ¬ IsOfFinOrder c) :
    ¬ IsOfFinOrder (c * c) := by
  intro hfin
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  refine hc (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * k, by omega, ?_⟩)
  rw [pow_mul, pow_two]
  exact hpow

/-- The first entry of a common-power-free pair has infinite order. -/
theorem not_isOfFinOrder_left_of_no_common_zpow {a b : G}
    (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) : ¬ IsOfFinOrder a := by
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have h1 : a ^ (n : ℤ) = b ^ (0 : ℤ) := by
    rw [zpow_zero, zpow_natCast, hpow]
  have hz : (n : ℤ) = 0 := (hab (n : ℤ) 0 h1).1
  omega

/-- The second entry of a common-power-free pair has infinite order. -/
theorem not_isOfFinOrder_right_of_no_common_zpow {a b : G}
    (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) : ¬ IsOfFinOrder b := by
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have h1 : a ^ (0 : ℤ) = b ^ (n : ℤ) := by
    rw [zpow_zero, zpow_natCast, hpow]
  have hz : (n : ℤ) = 0 := (hab 0 (n : ℤ) h1).2
  omega

/-- **`E(g)` is proper as soon as some pair has no common nonzero power.**  The
form that can be used before non-elementarity is known; see the section
docstring for the promotion argument. -/
theorem exists_notMem_elementaryClosure_of_no_common_zpow
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hcen : NoIndependentPairInCentralizer G x)
    (hbow : EscapingIsLoxodromic G x) (hindep : IndependentOfNoCommonZpow G x)
    {g : G} (hg : IsLoxodromic g x) {a b : G}
    (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) :
    ∃ f : G, f ∉ elementaryClosure g := by
  by_contra hall
  push_neg at hall
  obtain ⟨n₁, hn₁, hc₁⟩ :=
    exists_ne_zero_commute_sq_of_mem_elementaryClosure hiso hg (hall a)
  obtain ⟨n₂, hn₂, hc₂⟩ :=
    exists_ne_zero_commute_sq_of_mem_elementaryClosure hiso hg (hall b)
  have hu : IsLoxodromic (g ^ (n₁ * n₂)) x :=
    isLoxodromic_zpow hiso hg (mul_ne_zero hn₁ hn₂)
  have hcu₁ : Commute (a * a) (g ^ (n₁ * n₂)) := by
    have h := hc₁.zpow_right n₂
    rwa [← zpow_mul] at h
  have hcu₂ : Commute (b * b) (g ^ (n₁ * n₂)) := by
    have h := hc₂.zpow_right n₁
    rw [← zpow_mul, mul_comm n₂ n₁] at h
    exact h
  have halox : IsLoxodromic (a * a) x :=
    isLoxodromic_of_commute_of_escapingIsLoxodromic hiso hacy hbow
      (g ^ (n₁ * n₂)) (a * a) hu hcu₁
      (not_isOfFinOrder_mul_self (not_isOfFinOrder_left_of_no_common_zpow hab))
  have hblox : IsLoxodromic (b * b) x :=
    isLoxodromic_of_commute_of_escapingIsLoxodromic hiso hacy hbow
      (g ^ (n₁ * n₂)) (b * b) hu hcu₂
      (not_isOfFinOrder_mul_self (not_isOfFinOrder_right_of_no_common_zpow hab))
  have hsqa : (a : G) ^ (2 : ℤ) = a * a := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast, pow_two]
  have hsqb : (b : G) ^ (2 : ℤ) = b * b := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast, pow_two]
  have hnp : ∀ p q : ℤ, p ≠ 0 → q ≠ 0 → (a * a) ^ p ≠ (b * b) ^ q := by
    intro p q hp _ heq
    have h2 : a ^ (2 * p) = b ^ (2 * q) := by
      rw [zpow_mul, zpow_mul, hsqa, hsqb]
      exact heq
    have h3 : (2 : ℤ) * p = 0 := (hab (2 * p) (2 * q) h2).1
    exact hp (by omega)
  exact hcen (g ^ (n₁ * n₂)) (a * a) (b * b) hu halox hblox hcu₁ hcu₂
    (hindep (a * a) (b * b) halox hblox hnp)

/-- **The exclusion step of Osin's Theorem 1.1.**  A loxodromic element together
with a common-power-free pair gives two independent loxodromics: the loxodromic
and its conjugate by an element outside its elementary closure. -/
theorem actsNonElementarily_of_no_common_zpow
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hcen : NoIndependentPairInCentralizer G x)
    (hbow : EscapingIsLoxodromic G x) (hindep : IndependentOfNoCommonZpow G x)
    {g : G} (hg : IsLoxodromic g x) {a b : G}
    (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) :
    ActsNonElementarily (⊤ : Subgroup G) x := by
  obtain ⟨f, hf⟩ :=
    exists_notMem_elementaryClosure_of_no_common_zpow hiso hacy hcen hbow hindep
      hg hab
  exact actsNonElementarily_of_notMem_elementaryClosure hiso hindep
    (Subgroup.mem_top g) (Subgroup.mem_top f) hg hf

/-- **Osin's Lemma 7.1 from the sharpened inputs.**  The virtual-cyclicity
theorem is still used, through `ElementaryClosureVirtuallyCyclic`, at the one
place the `s`-normal argument needs it --- the twisted intersection inside two
elementary closures --- and no longer at the properness step. -/
theorem actsNonElementarily_of_isSNormal_of_centralizer
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hlox : HasLoxodromicOfUnbounded G x)
    (hindep : IndependentOfNoCommonZpow G x)
    (hvc : ElementaryClosureVirtuallyCyclic G x)
    (hcen : NoIndependentPairInCentralizer G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x)
    {N : Subgroup G} (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N x := by
  obtain ⟨g₁, -, -, -, hg₁, -, -⟩ := hG
  obtain ⟨g, hgN, hg⟩ := hlox N (not_bddOrbit_of_isSNormal hiso hacy hN hg₁)
  obtain ⟨h, hhN, hh⟩ : ∃ h : G, h ∈ N ∧ h ∉ elementaryClosure g := by
    by_contra hcon
    push_neg at hcon
    have hNle : N ≤ elementaryClosure g := by
      intro y hy
      exact hcon y hy
    obtain ⟨f, hf⟩ :=
      exists_notMem_elementaryClosure_of_centralizer hiso hcen hG hg
    have hk : IsLoxodromic (f * g * f⁻¹) x := isLoxodromic_conj hiso hg
    have hindgk : Independent g (f * g * f⁻¹) x := by
      refine hindep g (f * g * f⁻¹) hg hk ?_
      intro p r hp hr heq
      exact hf (mem_elementaryClosure_of_common_zpow_conj hp hr heq)
    have hTg : twistedIntersection N f⁻¹ ≤ elementaryClosure g := by
      intro y hy
      exact hNle (mem_twistedIntersection.mp hy).1
    have hTk : twistedIntersection N f⁻¹ ≤ elementaryClosure (f * g * f⁻¹) := by
      intro y hy
      refine mem_elementaryClosure_conj' (a := f) ?_
      have h2 := (mem_twistedIntersection.mp hy).2
      rw [inv_inv] at h2
      exact hNle h2
    exact not_infinite_le_inf_elementaryClosure hiso hvc hg hk hindgk hTg hTk
      (infinite_twistedIntersection hN f⁻¹)
  exact actsNonElementarily_of_notMem_elementaryClosure hiso hindep hgN hhN hg hh

end Action

end Elementary
end GGT
end GroupApproximation
