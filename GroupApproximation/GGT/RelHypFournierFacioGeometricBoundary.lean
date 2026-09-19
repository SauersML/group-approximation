import GroupApproximation.GGT.HullSCUnionGeometryVirtuallyCyclic
import GroupApproximation.GGT.RelHypHyperbolicPairReduction
import GroupApproximation.GGT.RelHypOsinTheorem24Verbatim

/-!
# The unconditional geometric boundary of the Fournier--Facio quotient

Two points around the source-faithful reduction of Fournier--Facio Proposition
2.3 admit complete in-repository proofs.

First, Osin's Theorem 2.4(5) has no further torsion-theoretic content to
formalize: its finite-order lifting clause sends torsion-freeness of the source
to torsion-freeness of the quotient by a three-line argument.  The remaining
debt is therefore the construction of the quotient carrying that clause, not
its use.

Second, a torsion-free non-elementary hyperbolic group unconditionally contains
two infinite-order elements with no equal nonzero powers.  This follows from
`HullSCUnionGeometry.isElementaryGroup_of_share`: if every nontrivial element
shared a power with one fixed infinite-order element, the group would be
elementary.

The latter conclusion is deliberately not mislabeled as Osin
non-commensurability.  `OsinCommensurable` permits an ambient conjugator.  The
last theorem below locates that gap exactly: for a direct-power-separated pair,
every commensurability witness has its conjugator outside the first element's
Osin elementary closure.  Thus all direct-power, torsion, finite-generation,
and centralizer bookkeeping is closed here; what remains is the geometric
exclusion of those exterior conjugators.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## 1.  The torsion clause of Osin 2.4 -/

/-- A finite-order lifting clause transfers power torsion-freeness from the
source to the target.  Surjectivity and every other quotient property are
irrelevant to this implication. -/
theorem isPowerTorsionFree_of_finiteOrder_lift {G Q : Type*} [Group G] [Group Q]
    (eta : G →* Q) (htf : IsPowerTorsionFree G)
    (hlift : ∀ q : Q, (∃ n : ℕ, 0 < n ∧ q ^ n = 1) →
      ∃ g : G, (∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧ eta g = q) :
    IsPowerTorsionFree Q := by
  intro q n hn hqn
  obtain ⟨g, ⟨m, hm, hgm⟩, hgq⟩ := hlift q ⟨n, hn, hqn⟩
  have hg1 : g = 1 := htf g m hm hgm
  rw [← hgq, hg1, map_one]

/-- In particular, clause (5) of an `IsOsin24Quotient` is exactly enough to
make its target torsion-free when its source is torsion-free. -/
theorem IsOsin24Quotient.isPowerTorsionFree {G Q : Type} [Group G] [Group Q]
    {iota : Type} {Hfam : iota → Subgroup G} {H : Subgroup G} {t : Set G}
    {eta : G →* Q} (hq : IsOsin24Quotient Hfam H t Q eta)
    (htf : IsPowerTorsionFree G) : IsPowerTorsionFree Q := by
  obtain ⟨-, -, -, -, -, hlift⟩ := hq
  exact isPowerTorsionFree_of_finiteOrder_lift eta htf hlift

/-! ## 2.  Direct-power separation from non-elementarity -/

/-- In a non-elementary hyperbolic group, every fixed infinite-order element
has a nontrivial element sharing no nonzero power with it.

This is the property-(T)-free form of
`HullSCUnionGeometry.exists_no_common_zpow`.  The latter used property (T) only
to establish non-elementarity; once non-elementarity is supplied directly,
the centralizer/finite-index argument is unconditional. -/
theorem exists_no_common_zpow_of_not_isElementaryGroup {H : Type} [Group H]
    (hhyp : Hyperbolic.IsHyperbolicGroup H) (hne : ¬ IsElementaryGroup H)
    {g : H} (hg : ¬ IsOfFinOrder g) :
    ∃ t : H, t ≠ 1 ∧
      ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hTsym, delta, hdelta⟩ := hhyp
  exact hne
    (HullSCUnionGeometry.isElementaryGroup_of_share
      (⟨(T : Set H), hTsym⟩ : Alphabet H) T.finite_toSet
      (isHyperbolicSpace_cayley_of_fourPoint _ hdelta) hg hcon)

/-- The strongest pair statement obtainable before controlling ambient
conjugators: both elements have infinite order, and no nonzero powers of them
are equal. -/
theorem exists_infiniteOrder_pair_no_common_zpow {H : Type} [Group H]
    (hne : IsNonElementaryHyperbolic H) (htf : IsPowerTorsionFree H) :
    ∃ g t : H,
      (∀ n : ℕ, 0 < n → g ^ n ≠ 1) ∧
      (∀ n : ℕ, 0 < n → t ^ n ≠ 1) ∧
      ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m := by
  haveI : Nontrivial H := nontrivial_of_not_isElementaryGroup hne.2
  obtain ⟨g, hg1⟩ := exists_ne (1 : H)
  have hgfin : ¬ IsOfFinOrder g := htf.not_isOfFinOrder hg1
  obtain ⟨t, ht1, hsep⟩ :=
    exists_no_common_zpow_of_not_isElementaryGroup hne.1 hne.2 hgfin
  refine ⟨g, t, ?_, ?_, hsep⟩
  · intro n hn hpow
    exact hg1 (htf g n hn hpow)
  · intro n hn hpow
    exact ht1 (htf t n hn hpow)

/-! ## 3.  Where the conjugator must live -/

/-- If `g` and `t` have no equal nonzero powers, a witness that they are Osin
commensurable cannot use a conjugator from `E_G(g)`.

Indeed an element of `E_G(g)` conjugates one positive power of `g` to itself or
its inverse.  Raising that equality by the exponent in the commensurability
witness and raising the witness by the positive elementary-closure exponent
eliminates the conjugator and produces forbidden equal nonzero powers of `g`
and `t`. -/
theorem not_mem_osinElementaryClosure_of_commensurability_witness
    {H : Type*} [Group H] {g t c : H} {k l : ℤ}
    (hk : k ≠ 0) (hl : l ≠ 0)
    (hconj : c⁻¹ * g ^ k * c = t ^ l)
    (hsep : ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m) :
    c ∉ osinElementaryClosure g := by
  rintro ⟨n, hn, hcase⟩
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hwitness : c⁻¹ * g ^ (k * (n : ℤ)) * c = t ^ (l * (n : ℤ)) := by
    calc
      c⁻¹ * g ^ (k * (n : ℤ)) * c = c⁻¹ * (g ^ k) ^ (n : ℤ) * c := by
        rw [zpow_mul]
      _ = (c⁻¹ * g ^ k * c) ^ (n : ℤ) := by
        simpa only [inv_inv] using
          (GGT.Elementary.conj_zpow_eq c⁻¹ (g ^ k) (n : ℤ))
      _ = (t ^ l) ^ (n : ℤ) := by rw [hconj]
      _ = t ^ (l * (n : ℤ)) := by rw [zpow_mul]
  rcases hcase with hsame | hinv
  · have hsameZ : c⁻¹ * g ^ (n : ℤ) * c = g ^ (n : ℤ) := by
      simpa [zpow_natCast] using hsame
    have hfix : c⁻¹ * g ^ ((n : ℤ) * k) * c = g ^ ((n : ℤ) * k) := by
      calc
        c⁻¹ * g ^ ((n : ℤ) * k) * c = c⁻¹ * (g ^ (n : ℤ)) ^ k * c := by
          rw [zpow_mul]
        _ = (c⁻¹ * g ^ (n : ℤ) * c) ^ k := by
          simpa only [inv_inv] using
            (GGT.Elementary.conj_zpow_eq c⁻¹ (g ^ (n : ℤ)) k)
        _ = (g ^ (n : ℤ)) ^ k := by rw [hsameZ]
        _ = g ^ ((n : ℤ) * k) := by rw [zpow_mul]
    apply hsep ((n : ℤ) * k) (l * (n : ℤ))
      (mul_ne_zero hn0 hk) (mul_ne_zero hl hn0)
    rw [← hfix, mul_comm (n : ℤ) k]
    exact hwitness
  · have hinvZ : c⁻¹ * g ^ (n : ℤ) * c = g ^ (-(n : ℤ)) := by
      simpa [zpow_natCast, zpow_neg] using hinv
    have hfix : c⁻¹ * g ^ ((n : ℤ) * k) * c = g ^ (-(n : ℤ) * k) := by
      calc
        c⁻¹ * g ^ ((n : ℤ) * k) * c = c⁻¹ * (g ^ (n : ℤ)) ^ k * c := by
          rw [zpow_mul]
        _ = (c⁻¹ * g ^ (n : ℤ) * c) ^ k := by
          simpa only [inv_inv] using
            (GGT.Elementary.conj_zpow_eq c⁻¹ (g ^ (n : ℤ)) k)
        _ = (g ^ (-(n : ℤ))) ^ k := by rw [hinvZ]
        _ = g ^ (-(n : ℤ) * k) := by rw [zpow_mul]
    apply hsep (-(n : ℤ) * k) (l * (n : ℤ))
      (mul_ne_zero (neg_ne_zero.mpr hn0) hk) (mul_ne_zero hl hn0)
    rw [← hfix, mul_comm (n : ℤ) k]
    exact hwitness

/-- Consequently, for a direct-power-separated pair, every hypothetical Osin
commensurability witness uses a conjugator outside `E_G(g)`.  This is the exact
remaining conjugator-sensitive geometric case. -/
theorem commensurability_conjugator_not_mem_osinElementaryClosure
    {H : Type*} [Group H] {g t : H}
    (hsep : ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m)
    (hcomm : OsinCommensurable g t) :
    ∃ k l : ℤ, ∃ c : H, k ≠ 0 ∧ l ≠ 0 ∧
      c⁻¹ * g ^ k * c = t ^ l ∧ c ∉ osinElementaryClosure g := by
  obtain ⟨k, l, c, hk, hl, hconj⟩ := hcomm
  exact ⟨k, l, c, hk, hl, hconj,
    not_mem_osinElementaryClosure_of_commensurability_witness hk hl hconj hsep⟩

end RelHyp
end GGT
end GroupApproximation
