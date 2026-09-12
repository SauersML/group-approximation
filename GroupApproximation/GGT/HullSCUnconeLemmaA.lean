import GroupApproximation.GGT.HullSCUnconeTriangleConnectors
import GroupApproximation.GGT.HullSCUnconePathPoints
import GroupApproximation.GGT.HullSCUnconeCosetCoordinates
import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 7: a component on a shared coset is covered by the other sides

Let `x`, `y`, `z` be joined by the chosen geodesic words of `J`, and let the letter at index `k` of
the side from `x` to `y` be a letter `gᵢᵉ` of a cyclic member, entering the coset `K`.  If one of the
two other sides has a component on `K`, every point of the expansion of that letter is within a
fixed distance, in the un-coned metric, of the guessed path of one of the two other sides
(`letter_point_near_sides`).

The proof reads the components on `K` in coordinates along the line `K = c⟨gᵢ⟩`
(`component_coordinates`), bounds the differences of their ends by the triangle connectors of
`GGT/HullSCUnconeTriangleConnectors.lean` and the finiteness of relative balls
(`natAbs_sub_le_of_connector`), and covers the interval of the letter by the chained intervals of
the other components (`cover_chain_one`, `cover_chain_two`).
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

namespace Uncone

section Letters

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- A component letter is a component constructor. -/
theorem exists_comp_of_isCompOf {lam : Λ} {a : RelLetter G Λ} (h : a.IsCompOf lam) :
    ∃ e : G, a = RelLetter.comp lam e := by
  cases a with
  | base x => exact False.elim h
  | comp mu e =>
      have hmu : mu = lam := h
      exact ⟨e, by rw [hmu]⟩

/-- **On a geodesic word a component letter is a whole component.** -/
theorem isComp_succ_of_isCompOf_geodesic (D : RelGenSet G Λ) {lam : Λ} {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {k : ℕ} (hk : k < w.length)
    (hc : (w[k]'hk).IsCompOf lam) : IsComp lam w k (k + 1) := by
  obtain ⟨s, k', hsk, hkk', hcomp⟩ := exists_isComp_of_isCompOf lam w k hk hc
  have hk' := isComp_eq_succ_of_isGeodesicWord D lam hw hcomp
  subst hk'
  have hs : s = k := by omega
  subst hs
  exact hcomp

end Letters

section Coordinates

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- The vertex after a cyclic letter `gᵢᵉ` is the vertex before it times `gᵢ` to the exponent of
`e`. -/
theorem vertex_succ_eq_mul_zpow (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) {f : Q}
    {w : List (RelLetter Q (Sum Lambda I))} (hlet : ∀ a ∈ w, J.IsLetter a) {i : I} {j : ℕ}
    (hj : j < w.length) {e : Q} (hletter : w[j]'hj = RelLetter.comp (Sum.inr i) e) :
    vertex f w (j + 1) = vertex f w j * g i ^ expo g i e := by
  have he : e ∈ Subgroup.zpowers (g i) := by
    rw [← hg i]
    have h0 := hlet _ (List.getElem_mem hj)
    rw [hletter] at h0
    exact h0
  rw [vertex_succ w f j hj, hletter]
  exact congrArg (vertex f w j * ·) (expo_spec g i he).symm

/-- **The ends of a cyclic letter in coordinates along a coset line through `q`.** -/
theorem component_coordinates (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) {f : Q}
    {w : List (RelLetter Q (Sum Lambda I))} (hlet : ∀ a ∈ w, J.IsLetter a) {i : I} {j : ℕ}
    (hj : j < w.length) {e : Q} (hletter : w[j]'hj = RelLetter.comp (Sum.inr i) e) (q : Q)
    (hcos : (QuotientGroup.mk (vertex f w j) : Q ⧸ J.fam (Sum.inr i)) = QuotientGroup.mk q) :
    ∃ a : ℤ, vertex f w j = q * g i ^ a ∧ vertex f w (j + 1) = q * g i ^ (a + expo g i e) := by
  have hmem : q⁻¹ * vertex f w j ∈ Subgroup.zpowers (g i) := by
    rw [← hg i]
    exact QuotientGroup.eq.mp hcos.symm
  have h1 : q * g i ^ expo g i (q⁻¹ * vertex f w j) = vertex f w j := by
    rw [expo_spec g i hmem, mul_inv_cancel_left]
  refine ⟨expo g i (q⁻¹ * vertex f w j), h1.symm, ?_⟩
  rw [vertex_succ_eq_mul_zpow J g hg hlet hj hletter, zpow_add, ← mul_assoc, h1]

/-- **A connector between two points of a coset line bounds their coordinate difference.** -/
theorem natAbs_sub_le_of_connector (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hinf : ∀ i : I, ¬ IsOfFinOrder (g i)) {T n : ℕ}
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) n → (expo g i e).natAbs ≤ T)
    (i : I) (q : Q) {A B : Q} {a b : ℤ} (hA : A = q * g i ^ a) (hB : B = q * g i ^ b)
    (h : A⁻¹ * B ∈ J.relBall (Sum.inr i) n) : (b - a).natAbs ≤ T := by
  subst hA hB
  exact natAbs_sub_le_of_mem_relBall J g hinf hT i q a b h

/-- The expansion of the letters up to and including the `j`-th fits in the whole expansion. -/
theorem length_expWord_take_add_le (g : I → Q) (w : List (RelLetter Q (Sum Lambda I))) {j : ℕ}
    (hj : j < w.length) :
    (expWord g (w.take j)).length + (expLetters g (w[j]'hj)).length ≤ (expWord g w).length := by
  rw [expWord_take_append g w j, expWord_drop_eq_cons g w hj, List.length_append,
    List.length_append]
  omega

theorem length_expLetters_inr (g : I → Q) (i : I) (e : Q) :
    (expLetters g (RelLetter.comp (Sum.inr i) e : RelLetter Q (Sum Lambda I))).length
      = (expo g i e).natAbs := by
  simp [expLetters]

/-- **Every point of a cyclic letter's coordinate interval is a point of the guessed path.** -/
theorem guessPath_coord (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y : Q) {j : ℕ}
    (hj : j < (geodWord J x y).length) {i : I} {e : Q}
    (hletter : (geodWord J x y)[j]'hj = RelLetter.comp (Sum.inr i) e) (q : Q) (a : ℤ)
    (hv : vertex x (geodWord J x y) j = q * g i ^ a) {s : ℤ}
    (hs1 : min 0 (expo g i e) ≤ s) (hs2 : s ≤ max 0 (expo g i e)) :
    ∃ n : ℕ, n ≤ guessLen J g x y ∧ guessPath J g x y n = q * g i ^ (a + s) := by
  have hlen : (expLetters g ((geodWord J x y)[j]'hj)).length = (expo g i e).natAbs := by
    rw [hletter]
    exact length_expLetters_inr g i e
  have hsn : s.natAbs ≤ (expLetters g ((geodWord J x y)[j]'hj)).length := by
    rw [hlen]
    omega
  have hsn' : s.natAbs ≤ (expo g i e).natAbs := by
    rw [← hlen]
    exact hsn
  refine ⟨(expWord g ((geodWord J x y).take j)).length + s.natAbs, ?_, ?_⟩
  · have hle := length_expWord_take_add_le g (geodWord J x y) hj
    unfold guessLen guessWord
    omega
  · rw [guessPath_in_letter J g hg x y hj hsn, hletter,
      prod_take_expLetters_inr (Lambda := Lambda) g i e hsn', hv, mul_assoc, ← zpow_add]
    have hexp : (a + if 0 ≤ expo g i e then (s.natAbs : ℤ) else -(s.natAbs : ℤ)) = a + s := by
      split_ifs with hnn <;> omega
    rw [hexp]

/-- **The point at offset `s` of a cyclic letter, in coordinates along its own entrance.** -/
theorem guessPath_letter_point (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y : Q) {j : ℕ}
    (hj : j < (geodWord J x y).length) {i : I} {e : Q}
    (hletter : (geodWord J x y)[j]'hj = RelLetter.comp (Sum.inr i) e) {s : ℕ}
    (hs : s ≤ (expo g i e).natAbs) :
    guessPath J g x y ((expWord g ((geodWord J x y).take j)).length + s)
      = vertex x (geodWord J x y) j * g i ^ (if 0 ≤ expo g i e then (s : ℤ) else -(s : ℤ)) := by
  have hsl : s ≤ (expLetters g ((geodWord J x y)[j]'hj)).length := by
    rw [hletter, length_expLetters_inr g i e]
    exact hs
  rw [guessPath_in_letter J g hg x y hj hsl, hletter,
    prod_take_expLetters_inr (Lambda := Lambda) g i e hs]

end Coordinates

section LemmaA

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- **A component on a shared coset is covered by the other sides.**

`hbnd` is the isolated-component bound of `J` for polygons with at most six sides, `Dc ≥ 4C`, and
`T` bounds the exponents in the relative balls of radius `Dc`.  If the letter at index `k` of the
side from `x` to `y` is `gᵢᵉ` and one of the other two sides has a component on the coset of its
entrance, every point of its expansion is within `T` of the guessed path of one of the other
sides. -/
theorem letter_point_near_sides (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (x y z : Q) {k : ℕ} (hk : k < (geodWord J x y).length) {i : I} {e : Q}
    (hletter : (geodWord J x y)[k]'hk = RelLetter.comp (Sum.inr i) e)
    (hconn : (∃ i₂ k₂ : ℕ, IsComp (Sum.inr i) (geodWord J x z) i₂ k₂ ∧
        (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i))
          = QuotientGroup.mk (vertex x (geodWord J x y) k)) ∨
      (∃ i₃ k₃ : ℕ, IsComp (Sum.inr i) (geodWord J z y) i₃ k₃ ∧
        (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i))
          = QuotientGroup.mk (vertex x (geodWord J x y) k)))
    {s : ℕ} (hs : s ≤ (expo g i e).natAbs) :
    (∃ n : ℕ, n ≤ guessLen J g x z ∧
        wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
          (guessPath J g x y ((expWord g ((geodWord J x y).take k)).length + s))
          (guessPath J g x z n) ≤ T) ∨
      (∃ n : ℕ, n ≤ guessLen J g z y ∧
        wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
          (guessPath J g x y ((expWord g ((geodWord J x y).take k)).length + s))
          (guessPath J g z y n) ≤ T) := by
  classical
  have hw₁ := geodWord_spec J x y
  have hw₂ := geodWord_spec J x z
  have hw₃ := geodWord_spec J z y
  have hc₁ : IsComp (Sum.inr i) (geodWord J x y) k (k + 1) :=
    isComp_succ_of_isCompOf_geodesic J hw₁ hk (by rw [hletter]; exact rfl)
  -- the letter, along the line through its entrance
  have hcIn : vertex x (geodWord J x y) k = vertex x (geodWord J x y) k * g i ^ (0 : ℤ) := by
    rw [zpow_zero, mul_one]
  have hcOut : vertex x (geodWord J x y) (k + 1)
      = vertex x (geodWord J x y) k * g i ^ expo g i e :=
    vertex_succ_eq_mul_zpow J g hg hw₁.1 hk hletter
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (if 0 ≤ expo g i e then (s : ℤ) else -(s : ℤ)) = t := ⟨_, rfl⟩
  have hpoint := guessPath_letter_point J g hg x y hk hletter hs
  rw [ht] at hpoint
  have ht1 : min 0 (expo g i e) ≤ t := by
    rw [← ht]
    split_ifs <;> omega
  have ht2 : t ≤ max 0 (expo g i e) := by
    rw [← ht]
    split_ifs <;> omega
  -- distances to points of the line through the entrance
  have hdist : ∀ b : ℤ, (t - b).natAbs ≤ T →
      wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
        (vertex x (geodWord J x y) k * g i ^ t) (vertex x (geodWord J x y) k * g i ^ b) ≤ T := by
    intro b hb
    have h0 := wordDist_mul_zpow_le J g hg hbaseInv i (vertex x (geodWord J x y) k) t b
    omega
  have hT4 : ∀ (i' : I) (e' : Q), e' ∈ J.relBall (Sum.inr i') (C * 4) →
      (expo g i' e').natAbs ≤ T :=
    fun i' e' he' => hT i' e' (relBall_mono_radius J (Sum.inr i') hDc he')
  by_cases h₂ : ∃ i₂ k₂ : ℕ, IsComp (Sum.inr i) (geodWord J x z) i₂ k₂ ∧
      (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i))
        = QuotientGroup.mk (vertex x (geodWord J x y) k)
  · obtain ⟨i₂, k₂, hc₂', hcos₂⟩ := h₂
    have hk₂eq := isComp_eq_succ_of_isGeodesicWord J (Sum.inr i) hw₂ hc₂'
    subst hk₂eq
    have hi₂ : i₂ < (geodWord J x z).length := by
      have := hc₂'.2.1
      omega
    obtain ⟨e₂, he₂⟩ := exists_comp_of_isCompOf (hc₂'.2.2.1 i₂ le_rfl (by omega) hi₂)
    obtain ⟨a₂, hv₂, hv₂'⟩ :=
      component_coordinates J g hg hw₂.1 hi₂ he₂ (vertex x (geodWord J x y) k) hcos₂
    -- entrances from `x`
    have hA1 : a₂.natAbs ≤ T := by
      have h0 := entranceConnector_mem_relBall_of_bound J (Sum.inr i) hbaseInv hbnd hDc hw₁ hw₂
        hc₁ hc₂' hcos₂.symm
      have h1 := natAbs_sub_le_of_connector J g hinf hT i _ hcIn hv₂ h0
      omega
    by_cases h₃ : ∃ i₃ k₃ : ℕ, IsComp (Sum.inr i) (geodWord J z y) i₃ k₃ ∧
        (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i))
          = QuotientGroup.mk (vertex x (geodWord J x y) k)
    · obtain ⟨i₃, k₃, hc₃', hcos₃⟩ := h₃
      have hk₃eq := isComp_eq_succ_of_isGeodesicWord J (Sum.inr i) hw₃ hc₃'
      subst hk₃eq
      have hi₃ : i₃ < (geodWord J z y).length := by
        have := hc₃'.2.1
        omega
      obtain ⟨e₃, he₃⟩ := exists_comp_of_isCompOf (hc₃'.2.2.1 i₃ le_rfl (by omega) hi₃)
      obtain ⟨a₃, hv₃, hv₃'⟩ :=
        component_coordinates J g hg hw₃.1 hi₃ he₃ (vertex x (geodWord J x y) k) hcos₃
      -- exits toward `y`
      have hA2 : (a₃ + expo g i e₃ - expo g i e).natAbs ≤ T := by
        have h0 := exitConnector_mem_relBall J (Sum.inr i) hbaseInv hbnd hDc hw₁ hw₃ hc₁ hc₃'
          hcos₃.symm
        exact natAbs_sub_le_of_connector J g hinf hT i _ hcOut hv₃' h0
      -- the exit of the second side and the entrance of the third, at `z`
      have hA3 : (a₃ - (a₂ + expo g i e₂)).natAbs ≤ T := by
        have h0 := exitEntranceConnector_mem_relBall J (Sum.inr i) hbaseInv hbnd hDc hw₂ hw₃
          hc₂' hc₃' (hcos₂.trans hcos₃.symm)
        exact natAbs_sub_le_of_connector J g hinf hT i _ hv₂' hv₃ h0
      rcases cover_chain_two T a₂ (expo g i e₂) a₃ (expo g i e₃) (expo g i e) t hA1 hA3 hA2 ht1
          ht2 with ⟨s₂, hs₂1, hs₂2, hs₂⟩ | ⟨s₃, hs₃1, hs₃2, hs₃⟩
      · obtain ⟨n, hn, hpn⟩ := guessPath_coord J g hg x z hi₂ he₂ _ a₂ hv₂ hs₂1 hs₂2
        refine Or.inl ⟨n, hn, ?_⟩
        rw [hpoint, hpn]
        exact hdist (a₂ + s₂) hs₂
      · obtain ⟨n, hn, hpn⟩ := guessPath_coord J g hg z y hi₃ he₃ _ a₃ hv₃ hs₃1 hs₃2
        refine Or.inr ⟨n, hn, ?_⟩
        rw [hpoint, hpn]
        exact hdist (a₃ + s₃) hs₃
    · -- the third side does not reach the coset
      have hno₃ : ∀ i₃ k₃ : ℕ, IsComp (Sum.inr i) (geodWord J z y) i₃ k₃ →
          (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i))
            ≠ QuotientGroup.mk (vertex x (geodWord J x y) k) :=
        fun i₃ k₃ hc₃ hcos₃ => h₃ ⟨i₃, k₃, hc₃, hcos₃⟩
      have hA4 : (a₂ + expo g i e₂ - expo g i e).natAbs ≤ T := by
        have h0 := exitConnector_of_noComp J (Sum.inr i) hbaseInv hbnd hw₁ hw₂ hw₃ hc₁ hc₂'
          hcos₂.symm hno₃
        have h1 := natAbs_sub_le_of_connector J g hinf hT4 i _ hv₂' hcOut h0
        omega
      obtain ⟨s₂, hs₂1, hs₂2, hs₂⟩ :=
        cover_chain_one T a₂ (expo g i e₂) (expo g i e) t hA1 hA4 ht1 ht2
      obtain ⟨n, hn, hpn⟩ := guessPath_coord J g hg x z hi₂ he₂ _ a₂ hv₂ hs₂1 hs₂2
      refine Or.inl ⟨n, hn, ?_⟩
      rw [hpoint, hpn]
      exact hdist (a₂ + s₂) hs₂
  · -- only the third side reaches the coset
    have hno₂ : ∀ i₂ k₂ : ℕ, IsComp (Sum.inr i) (geodWord J x z) i₂ k₂ →
        (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i))
          ≠ QuotientGroup.mk (vertex x (geodWord J x y) k) :=
      fun i₂ k₂ hc₂ hcos₂ => h₂ ⟨i₂, k₂, hc₂, hcos₂⟩
    obtain ⟨i₃, k₃, hc₃', hcos₃⟩ := hconn.resolve_left h₂
    have hk₃eq := isComp_eq_succ_of_isGeodesicWord J (Sum.inr i) hw₃ hc₃'
    subst hk₃eq
    have hi₃ : i₃ < (geodWord J z y).length := by
      have := hc₃'.2.1
      omega
    obtain ⟨e₃, he₃⟩ := exists_comp_of_isCompOf (hc₃'.2.2.1 i₃ le_rfl (by omega) hi₃)
    obtain ⟨a₃, hv₃, hv₃'⟩ :=
      component_coordinates J g hg hw₃.1 hi₃ he₃ (vertex x (geodWord J x y) k) hcos₃
    -- entrances, the second side not reaching the coset
    have hA5 : a₃.natAbs ≤ T := by
      have h0 := entranceConnector_of_noComp J (Sum.inr i) hbaseInv hbnd hw₁ hw₂ hw₃ hc₁ hc₃'
        hcos₃.symm hno₂
      have h1 := natAbs_sub_le_of_connector J g hinf hT4 i _ hv₃ hcIn h0
      omega
    have hA2 : (a₃ + expo g i e₃ - expo g i e).natAbs ≤ T := by
      have h0 := exitConnector_mem_relBall J (Sum.inr i) hbaseInv hbnd hDc hw₁ hw₃ hc₁ hc₃'
        hcos₃.symm
      exact natAbs_sub_le_of_connector J g hinf hT i _ hcOut hv₃' h0
    obtain ⟨s₃, hs₃1, hs₃2, hs₃⟩ :=
      cover_chain_one T a₃ (expo g i e₃) (expo g i e) t hA5 hA2 ht1 ht2
    obtain ⟨n, hn, hpn⟩ := guessPath_coord J g hg z y hi₃ he₃ _ a₃ hv₃ hs₃1 hs₃2
    refine Or.inr ⟨n, hn, ?_⟩
    rw [hpoint, hpn]
    exact hdist (a₃ + s₃) hs₃

end LemmaA

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.exists_comp_of_isCompOf
#audit_axioms GroupApproximation.GGT.Uncone.isComp_succ_of_isCompOf_geodesic
#audit_axioms GroupApproximation.GGT.Uncone.vertex_succ_eq_mul_zpow
#audit_axioms GroupApproximation.GGT.Uncone.component_coordinates
#audit_axioms GroupApproximation.GGT.Uncone.natAbs_sub_le_of_connector
#audit_axioms GroupApproximation.GGT.Uncone.guessPath_coord
#audit_axioms GroupApproximation.GGT.Uncone.guessPath_letter_point
#audit_axioms GroupApproximation.GGT.Uncone.letter_point_near_sides
