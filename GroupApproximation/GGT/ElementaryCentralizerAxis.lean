import GroupApproximation.GGT.ElementaryProperClosure

/-!
# The centralizer of a loxodromic element, from one Morse statement

Osin, *Acylindrically hyperbolic groups*, Corollary 6.9: the centralizer of a
loxodromic element of an acylindrical action is elementary.  This module proves
it, and over a torsion-free ambient group it also removes Theorem 6.8 from every
consumer in this development, against a single named Morse output.

## The named input

    CentralizerOrbitNearAxis G x :
      ∀ q, IsLoxodromic q x → ∃ K ≥ 0, ∀ c, Commute c q → ∀ k : ℤ,
        ∃ j : ℤ, dist ((c ^ k) • x) ((q ^ j) • x) ≤ K

**Why the constant is uniform in `c` and `k`, which is the whole content.**  Let
`Λ = {qⁿ x}` be the orbit of `q`.  If `c` commutes with `q` then
`cᵏ · Λ = {qⁿ (cᵏ x)}` is again an orbit of `q`, so it is a quasi-geodesic with
*the same* constants as `Λ` --- translation length `τ(q)` below, one-step
displacement `d(x, qx)` above --- and, since `cᵏ` commutes with `q`, it has the
same pair of endpoints.  Morse stability for quasi-geodesics with equal
constants and equal endpoints gives a Hausdorff bound depending only on `δ` and
those constants, so it does not see `c` or `k` at all.  The point `cᵏ x` lies on
`cᵏ · Λ`, so it is within that bound of `Λ`.

## What acylindricity supplies free of charge

The pigeonhole
`HullGeometry.acylindrical_common_power_of_two_orbit_fellow_travel` wants the
matched orbit points close at **two** basepoints far apart.  In the commuting
case the second basepoint costs nothing: `cᴬ` and `q^B` both commute with `q^M`,
so translating the whole configuration by `q^M` is an isometry of the pair, and
the closeness at `x` transports verbatim to `q^M x`.  Taking `M` large makes the
two basepoints as far apart as acylindricity demands, because `q` is loxodromic.
That is `dist_smul_of_commute_translate`, and it is why this argument needs only
a one-basepoint Morse statement.

The exponent families must both be injective.  The first is chosen
(`exists_injective_separated_family`: exponents spaced by more than `2ε / τ(c)`),
and the second is then injective for free --- two matched pairs sharing a
partner would put their `c`-orbit points `2ε` apart, against the spacing.

## The consequences

* `exists_common_zpow_of_commute_of_orbitNearAxis` --- a loxodromic element
  commuting with a loxodromic `q` shares a nonzero power with `q`.
* `noIndependentPairInCentralizer_of_orbitNearAxis` --- Corollary 6.9, i.e.
  `NoIndependentPairInCentralizer`.  Two independent loxodromics in `C(q)` would
  each share a power with `q`, so with each other, and a common power destroys
  independence (`not_independent_of_common_zpow`).

## Theorem 6.8 disappears over a torsion-free ambient

`ElementaryClosureVirtuallyCyclic` was used in `GGT.ElementaryOsinSNormal` only
through `not_infinite_le_inf_elementaryClosure`, inside the `s`-normal argument.
Over a torsion-free ambient that use is replaced here with no reference to
Theorem 6.8 at all:

* every `c ≠ 1` has infinite order, so an infinite subgroup has a nontrivial
  element;
* for `c ∈ E(g)`, `c²` commutes with a nonzero power `gⁿ`
  (`exists_ne_zero_commute_sq_of_mem_elementaryClosure`, which is where the
  translation-length normalisation is spent), and `c²` has infinite order, so
  Bowditch's dichotomy makes it loxodromic;
* the theorem above then gives `c²` a common power with `gⁿ`, so `c` has one
  with `g`.

So a nontrivial element of `K ≤ E(g) ⊓ E(k)` shares a power with `g` and with
`k`, giving `g` and `k` a common power and contradicting their independence.
`actsNonElementarily_of_isSNormal_of_torsionFree` is Osin's Lemma 7.1 with that
substitution made: its residuals are `CentralizerOrbitNearAxis`,
`EscapingIsLoxodromic`, `IndependentOfNoCommonZpow` and
`HasLoxodromicOfUnbounded`, and `ElementaryClosureVirtuallyCyclic` is not among
them.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

section Input

/-- **The Morse output this module consumes.**  For a loxodromic `q` there is
one constant `K` such that every power of every element commuting with `q` lies
within `K` of the orbit of `q`.  Uniformity in the commuting element and in the
power is the content; see the module docstring. -/
def CentralizerOrbitNearAxis (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ q : G, IsLoxodromic q x → ∃ K : ℝ, 0 ≤ K ∧
    ∀ c : G, Commute c q → ∀ k : ℤ, ∃ j : ℤ, dist ((c ^ k) • x) ((q ^ j) • x) ≤ K

end Input

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## A spaced family of exponents -/

/-- Arbitrarily many integer exponents, injective and pairwise separated by more
than a prescribed amount once scaled by a positive rate.  The exponents are the
multiples of one integer larger than `ε / τ`. -/
theorem exists_injective_separated_family {τ ε : ℝ} (hτ : 0 < τ) (n : ℕ) :
    ∃ A : Fin n → ℤ, Function.Injective A ∧
      ∀ i j : Fin n, i ≠ j → ε < τ * |((A j - A i : ℤ) : ℝ)| := by
  obtain ⟨S, hS⟩ := exists_nat_gt (max (ε / τ) 1)
  have hS1 : (1 : ℝ) < (S : ℝ) := lt_of_le_of_lt (le_max_right _ _) hS
  have hSpos : 0 < S := by exact_mod_cast lt_trans zero_lt_one hS1
  have hSne : (S : ℤ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hSR : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hεS : ε < τ * (S : ℝ) := by
    have h1 : ε / τ < (S : ℝ) := lt_of_le_of_lt (le_max_left _ _) hS
    rw [div_lt_iff₀ hτ] at h1
    rw [mul_comm]
    exact h1
  refine ⟨fun i => (S : ℤ) * (i.val : ℤ), ?_, ?_⟩
  · intro i j hij
    have h1 : (S : ℤ) * (i.val : ℤ) = (S : ℤ) * (j.val : ℤ) := hij
    have h2 : (i.val : ℤ) = (j.val : ℤ) := mul_left_cancel₀ hSne h1
    have h3 : i.val = j.val := by exact_mod_cast h2
    exact Fin.val_injective h3
  · intro i j hij
    show ε < τ * |(((S : ℤ) * (j.val : ℤ) - (S : ℤ) * (i.val : ℤ) : ℤ) : ℝ)|
    have hene : ((j.val : ℤ) - (i.val : ℤ)) ≠ 0 := by
      intro h
      have h2 : i.val = j.val := by omega
      exact hij (Fin.val_injective h2)
    have hEone : (1 : ℝ) ≤ |((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ)| := by
      rcases lt_trichotomy ((j.val : ℤ) - (i.val : ℤ)) 0 with h | h | h
      · have h1 : ((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ) < 0 := by exact_mod_cast h
        rw [abs_of_neg h1]
        have h2 : ((j.val : ℤ) - (i.val : ℤ)) ≤ -1 := by omega
        have h3 : ((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h2
        linarith
      · exact absurd h hene
      · have h1 : (0 : ℝ) < ((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ) := by
          exact_mod_cast h
        rw [abs_of_pos h1]
        have h2 : (1 : ℤ) ≤ ((j.val : ℤ) - (i.val : ℤ)) := by omega
        exact_mod_cast h2
    have hcast : ((((S : ℤ) * (j.val : ℤ) - (S : ℤ) * (i.val : ℤ)) : ℤ) : ℝ)
        = (S : ℝ) * ((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hcast, abs_mul, abs_of_nonneg hSR]
    have hmul : (S : ℝ) * 1 ≤ (S : ℝ) * |((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ)| :=
      mul_le_mul_of_nonneg_left hEone hSR
    have hfinal : τ * ((S : ℝ) * 1)
        ≤ τ * ((S : ℝ) * |((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℝ)|) :=
      mul_le_mul_of_nonneg_left hmul (le_of_lt hτ)
    rw [mul_one] at hfinal
    linarith

/-! ## The second basepoint is free in the commuting case -/

/-- **Translating the configuration along the axis is an isometry of it.**  If
`c` commutes with `q` then `c^A` and `q^B` both commute with `q^M`, so moving
both orbit points by `q^M` changes neither their distance nor which pair they
are.  This is what lets one closeness bound at `x` serve both basepoints of the
acylindricity condition. -/
theorem dist_smul_of_commute_translate (hiso : IsIsometricAction G X)
    {q c : G} (hcq : Commute c q) (A B : ℤ) (M : ℕ) (x : X) :
    dist ((c ^ A) • ((q ^ M) • x)) ((q ^ B) • ((q ^ M) • x))
      = dist ((c ^ A) • x) ((q ^ B) • x) := by
  have h1 : (c ^ A) • ((q ^ M) • x) = (q ^ M) • ((c ^ A) • x) := by
    rw [← mul_smul, ← mul_smul, ((hcq.zpow_left A).pow_right M).eq]
  have h2 : (q ^ B) • ((q ^ M) • x) = (q ^ M) • ((q ^ B) • x) := by
    rw [← mul_smul, ← mul_smul, (((Commute.refl q).zpow_left B).pow_right M).eq]
  rw [h1, h2]
  exact hiso (q ^ M) ((c ^ A) • x) ((q ^ B) • x)

/-! ## A common power inside the centralizer -/

/-- **A loxodromic element commuting with a loxodromic element shares a nonzero
power with it.**

Acylindricity is used once, through
`acylindrical_common_power_of_two_orbit_fellow_travel`; the Morse input is used
once, to produce the partner exponents; and the commuting hypothesis is used
twice, to make the second basepoint free and to keep the whole configuration on
one axis. -/
theorem exists_common_zpow_of_commute_of_orbitNearAxis
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) {q c : G}
    (hq : IsLoxodromic q x) (hc : IsLoxodromic c x) (hcq : Commute c q) :
    ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ c ^ p = q ^ r := by
  obtain ⟨K, hK0, hK⟩ := hnear q hq
  have hε : (0 : ℝ) < K + 1 := by linarith
  obtain ⟨R, N, hRN⟩ :=
    acylindrical_common_power_of_two_orbit_fellow_travel hiso hacy hε
  -- a second basepoint, far out along the axis of `q`
  have hev := hq.isEscaping.eventually_ge_atTop R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  have hfar : R ≤ dist x ((q ^ M) • x) := hM M le_rfl
  -- the spaced family of `c`-exponents, and their partners on the axis
  have hτ : 0 < stableTranslation c x :=
    stableTranslation_pos_of_isLoxodromic hiso hc
  obtain ⟨A, hAinj, hAsep⟩ :=
    exists_injective_separated_family (τ := stableTranslation c x)
      (ε := 2 * (K + 1)) hτ (N + 1)
  choose B hB using fun i : Fin (N + 1) => hK c hcq (A i)
  -- the partners are distinct, because the `c`-exponents are spaced
  have hBinj : Function.Injective B := by
    intro i j hij
    by_contra hne
    have h1 := hB i
    have h2 := hB j
    have hswap : dist ((q ^ (B i)) • x) ((c ^ (A j)) • x)
        = dist ((c ^ (A j)) • x) ((q ^ (B j)) • x) := by
      rw [dist_comm, hij]
    have htri :=
      dist_triangle ((c ^ (A i)) • x) ((q ^ (B i)) • x) ((c ^ (A j)) • x)
    rw [hswap] at htri
    have horbit := dist_zpow_orbit hiso c x (A i) (A j)
    have hlow := mul_le_dist_zpow hiso c x (A j - A i)
    rw [← horbit] at hlow
    have hsep := hAsep i j hne
    linarith
  -- the matched pairs, at both basepoints
  have hclose : ∀ i : Fin (N + 1),
      dist ((c ^ (A i)) • x) ((q ^ (B i)) • x) ≤ K + 1 ∧
        dist ((c ^ (A i)) • ((q ^ M) • x)) ((q ^ (B i)) • ((q ^ M) • x))
          ≤ K + 1 := by
    intro i
    refine ⟨by linarith [hB i], ?_⟩
    rw [dist_smul_of_commute_translate hiso hcq (A i) (B i) M x]
    linarith [hB i]
  obtain ⟨i, j, -, hpne, hrne, hpow⟩ :=
    hRN x ((q ^ M) • x) hfar c q A B hAinj hBinj hclose
  exact ⟨A i - A j, B i - B j, hpne, hrne, hpow⟩

/-- **Osin, Corollary 6.9.**  The centralizer of a loxodromic element contains
no two independent loxodromic elements: each would share a nonzero power with
the central element, so with the other, and a common power destroys
independence. -/
theorem noIndependentPairInCentralizer_of_orbitNearAxis
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) :
    NoIndependentPairInCentralizer G x := by
  intro u a b hu ha hb hau hbu hind
  obtain ⟨p, r, hp, hr, hpu⟩ :=
    exists_common_zpow_of_commute_of_orbitNearAxis hiso hacy hnear hu ha hau
  obtain ⟨p', r', hp', hr', hpu'⟩ :=
    exists_common_zpow_of_commute_of_orbitNearAxis hiso hacy hnear hu hb hbu
  have hcommon : a ^ (p * r') = b ^ (p' * r) := by
    calc a ^ (p * r') = (a ^ p) ^ r' := by rw [zpow_mul]
      _ = (u ^ r) ^ r' := by rw [hpu]
      _ = u ^ (r * r') := by rw [← zpow_mul]
      _ = u ^ (r' * r) := by rw [mul_comm r r']
      _ = (u ^ r') ^ r := by rw [zpow_mul]
      _ = (b ^ p') ^ r := by rw [hpu']
      _ = b ^ (p' * r) := by rw [← zpow_mul]
  exact not_independent_of_common_zpow hiso ha (mul_ne_zero hp hr')
    (mul_ne_zero hp' hr) hcommon hind

/-! ## Over a torsion-free ambient, Theorem 6.8 is not needed -/

/-- **Every nontrivial element of `E(g)` shares a nonzero power with `g`**, over
a torsion-free ambient group, with no appeal to virtual cyclicity.

The square of the element commutes with a nonzero power of `g`, has infinite
order, and is therefore loxodromic by Bowditch's dichotomy; the centralizer
theorem above then supplies the common power. -/
theorem exists_common_zpow_of_mem_elementaryClosure_of_axis
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) (hbow : EscapingIsLoxodromic G x)
    (htf : IsPowerTorsionFree G) {g c : G} (hg : IsLoxodromic g x)
    (hc : c ∈ elementaryClosure g) (hc1 : c ≠ 1) :
    ∃ i m : ℤ, i ≠ 0 ∧ m ≠ 0 ∧ g ^ i = c ^ m := by
  obtain ⟨n, hn, hcomm⟩ :=
    exists_ne_zero_commute_sq_of_mem_elementaryClosure hiso hg hc
  have hgn : IsLoxodromic (g ^ n) x := isLoxodromic_zpow hiso hg hn
  have hc2ne : c * c ≠ 1 := by
    intro h
    refine htf.not_isOfFinOrder hc1 ?_
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩
    rw [pow_two]
    exact h
  have hc2lox : IsLoxodromic (c * c) x :=
    isLoxodromic_of_commute_of_escapingIsLoxodromic hiso hacy hbow (g ^ n)
      (c * c) hgn hcomm (htf.not_isOfFinOrder hc2ne)
  obtain ⟨p, r, hp, hr, hpow⟩ :=
    exists_common_zpow_of_commute_of_orbitNearAxis hiso hacy hnear hgn hc2lox
      hcomm
  have hsq : c ^ (2 : ℤ) = c * c := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast, pow_two]
  refine ⟨n * r, 2 * p, mul_ne_zero hn hr,
    mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hp, ?_⟩
  calc g ^ (n * r) = (g ^ n) ^ r := by rw [zpow_mul]
    _ = (c * c) ^ p := hpow.symm
    _ = (c ^ (2 : ℤ)) ^ p := by rw [hsq]
    _ = c ^ (2 * p) := by rw [← zpow_mul]

/-- **Two independent elementary closures share no infinite subgroup**, over a
torsion-free ambient, from the centralizer theorem and Bowditch's dichotomy
rather than from Theorem 6.8. -/
theorem not_infinite_le_inf_elementaryClosure_of_torsionFree
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) (hbow : EscapingIsLoxodromic G x)
    (htf : IsPowerTorsionFree G) {g k : G} (hg : IsLoxodromic g x)
    (hk : IsLoxodromic k x) (hind : Independent g k x) {K : Subgroup G}
    (hKg : K ≤ elementaryClosure g) (hKk : K ≤ elementaryClosure k)
    (hKinf : ((K : Subgroup G) : Set G).Infinite) : False := by
  obtain ⟨c, hcK, hc1⟩ : ∃ c : G, c ∈ K ∧ c ≠ 1 := by
    by_contra hnone
    push_neg at hnone
    refine hKinf (Set.Finite.subset (Set.finite_singleton (1 : G)) ?_)
    intro y hy
    rw [Set.mem_singleton_iff]
    exact hnone y hy
  obtain ⟨i₁, m₁, hi₁, hm₁, he₁⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_of_axis hiso hacy hnear hbow htf
      hg (hKg hcK) hc1
  obtain ⟨i₂, m₂, hi₂, hm₂, he₂⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_of_axis hiso hacy hnear hbow htf
      hk (hKk hcK) hc1
  have hcommon : g ^ (i₁ * m₂) = k ^ (i₂ * m₁) := by
    calc g ^ (i₁ * m₂) = (g ^ i₁) ^ m₂ := by rw [zpow_mul]
      _ = (c ^ m₁) ^ m₂ := by rw [he₁]
      _ = c ^ (m₁ * m₂) := by rw [← zpow_mul]
      _ = c ^ (m₂ * m₁) := by rw [mul_comm m₁ m₂]
      _ = (c ^ m₂) ^ m₁ := by rw [zpow_mul]
      _ = (k ^ i₂) ^ m₁ := by rw [← he₂]
      _ = k ^ (i₂ * m₁) := by rw [← zpow_mul]
  exact not_independent_of_common_zpow hiso hg (mul_ne_zero hi₁ hm₂)
    (mul_ne_zero hi₂ hm₁) hcommon hind

/-- **Osin's Lemma 7.1 over a torsion-free ambient group.**  The residuals are
`CentralizerOrbitNearAxis`, `EscapingIsLoxodromic`, `IndependentOfNoCommonZpow`
and `HasLoxodromicOfUnbounded`; `ElementaryClosureVirtuallyCyclic` is gone,
replaced at its one use by the centralizer theorem. -/
theorem actsNonElementarily_of_isSNormal_of_torsionFree
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) (hbow : EscapingIsLoxodromic G x)
    (hlox : HasLoxodromicOfUnbounded G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x)
    {N : Subgroup G} (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N x := by
  have hcen : NoIndependentPairInCentralizer G x :=
    noIndependentPairInCentralizer_of_orbitNearAxis hiso hacy hnear
  obtain ⟨g₁, -, -, -, hg₁, -, -⟩ := id hG
  obtain ⟨g, hgN, hg⟩ := hlox N (not_bddOrbit_of_isSNormal hiso hacy hN hg₁)
  obtain ⟨h, hhN, hh⟩ : ∃ h : G, h ∈ N ∧ h ∉ elementaryClosure g := by
    by_contra hcon
    push_neg at hcon
    have hNle : N ≤ elementaryClosure g := by
      intro y hy
      exact hcon y hy
    obtain ⟨f, hf⟩ :=
      exists_notMem_elementaryClosure_of_centralizer hiso hcen hG hg
    have hkl : IsLoxodromic (f * g * f⁻¹) x := isLoxodromic_conj hiso hg
    have hindgk : Independent g (f * g * f⁻¹) x := by
      refine hindep g (f * g * f⁻¹) hg hkl ?_
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
    exact not_infinite_le_inf_elementaryClosure_of_torsionFree hiso hacy hnear
      hbow htf hg hkl hindgk hTg hTk (infinite_twistedIntersection hN f⁻¹)
  exact actsNonElementarily_of_notMem_elementaryClosure hiso hindep hgN hhN hg hh

end Action

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree

variable {G : Type u} [Group G]

/-- **The manuscript's statement over a torsion-free ambient group**, at Hull's
Cayley graph.  This is `HullInputsCorrected.osinNonElementary` restricted to the
torsion-free case, which is the only case `lem:saturation` uses, with Theorem 6.8
removed from the residuals. -/
theorem osinNonElementary_of_torsionFree (A : HullGeneratingSet G)
    (hnear : CentralizerOrbitNearAxis G (Cayley.base A.alphabet))
    (hbow : EscapingIsLoxodromic G (Cayley.base A.alphabet))
    (hlox : HasLoxodromicOfUnbounded G (Cayley.base A.alphabet))
    (hindep : IndependentOfNoCommonZpow G (Cayley.base A.alphabet))
    (htf : IsPowerTorsionFree G) (N : Subgroup G)
    (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  actsNonElementarily_of_isSNormal_of_torsionFree A.isometric A.acylindrical
    hnear hbow hlox hindep htf A.nonElementary hN

end Cayley

end Elementary
end GGT
end GroupApproximation
