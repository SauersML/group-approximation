import GroupApproximation.BirmanGenusThree.Section3Algebra

/-!
# Chen–Salter, Corollary 3.4 and Lemma 3.5

From the key step `zero_or_id_of_ne` this file proves:
- `corollary_3_4`: either `f(α^k) = α^k` for every simple `α` and every `α^k ∈ H` (Case A), or
  `f(α^k) = 1` for all of them (Case B). This is Chen–Salter's Lemma 3.3 together with Corollary 3.4
  (arXiv:1804.11235v1).
- `lemma_3_5`: in Case A, `f` is the inclusion of `H`.

`HasPowersIn H` says that every element has a nonzero power in `H`; a finite-index subgroup has it
(`hasPowersIn_of_index_ne_zero`).
-/

namespace GroupApproximation.BirmanGenusThree.Section3

/-- Every element of `G` has a nonzero power in `H`. -/
def HasPowersIn {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ g : G, ∃ n : ℤ, n ≠ 0 ∧ g ^ n ∈ H

/-- A finite-index subgroup contains a nonzero power of every element. -/
theorem hasPowersIn_of_index_ne_zero {G : Type*} [Group G] {H : Subgroup G} (h : H.index ≠ 0) :
    HasPowersIn H := by
  intro g
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero h g
  exact ⟨n, by omega, by rw [zpow_natCast]; exact hgn⟩

variable {G : Type*} [Group G] [IsMulTorsionFree G] {S : Set G} {H : Subgroup G} {f : H →* G}

omit [IsMulTorsionFree G] in
private lemma mk_zpow_zero {α : G} (hk : α ^ (0 : ℤ) ∈ H) : (⟨α ^ (0 : ℤ), hk⟩ : H) = 1 := by
  ext; simp

omit [IsMulTorsionFree G] in
private lemma ne_inv_symm {α β : G} (h : β ≠ α⁻¹) : α ≠ β⁻¹ := by
  rintro rfl; exact h (inv_inv β).symm

/-- Each power of a simple element is sent to `1` or to itself. -/
theorem zero_or_id (hG : PowConjRigid G) (hC : CommonPowers G) (hS : SimpleSystem S)
    (hH : HasPowersIn H) (hf : PowerExponentForm S H f) {α : G} (hαS : α ∈ S) {k : ℤ}
    (hα : α ^ k ∈ H) : f ⟨α ^ k, hα⟩ = 1 ∨ f ⟨α ^ k, hα⟩ = α ^ k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨β, hβS, hne, hne'⟩ := hS.exists_other α hαS
  obtain ⟨ℓ, hℓ, hβ⟩ := hH β
  have hβ1 : β ≠ 1 := fun h => hS.one_notMem (h ▸ hβS)
  have hP : f ⟨β ^ ℓ, hβ⟩ = β ^ ℓ :=
    (zero_or_id_of_ne hG hC hS hf hαS hβS hne hne' hα hβ).resolve_left hcon.1
  have hZ : f ⟨β ^ ℓ, hβ⟩ = 1 :=
    (zero_or_id_of_ne hG hC hS hf hβS hαS (Ne.symm hne) (ne_inv_symm hne') hβ hα).resolve_right
      hcon.2
  have : β ^ ℓ = 1 := hP.symm.trans hZ
  exact hℓ ((IsMulTorsionFree.zpow_eq_one_iff_right hβ1).1 this)

/-- A mixed pair with `α' ≠ α^{±1}` is impossible. -/
private lemma mixed_false_of_ne (hG : PowConjRigid G) (hC : CommonPowers G) (hS : SimpleSystem S)
    (hf : PowerExponentForm S H f) {α α' : G} (hαS : α ∈ S) (hα'S : α' ∈ S) (hne : α' ≠ α)
    (hne' : α' ≠ α⁻¹) {k k' : ℤ} (hk : k ≠ 0) (hk' : k' ≠ 0) (hα : α ^ k ∈ H) (hα' : α' ^ k' ∈ H)
    (hP : f ⟨α ^ k, hα⟩ = α ^ k) (hZ : f ⟨α' ^ k', hα'⟩ = 1) : False := by
  have hα1 : α ≠ 1 := fun h => hS.one_notMem (h ▸ hαS)
  have hα'1 : α' ≠ 1 := fun h => hS.one_notMem (h ▸ hα'S)
  rcases zero_or_id_of_ne hG hC hS hf hαS hα'S hne hne' hα hα' with h | h
  · exact hk ((IsMulTorsionFree.zpow_eq_one_iff_right hα1).1 (hP.symm.trans h))
  · exact hk' ((IsMulTorsionFree.zpow_eq_one_iff_right hα'1).1 (h.symm.trans hZ))

/-- A power of a simple element fixed by `f` and a power of a simple element killed by `f` cannot
coexist. -/
theorem not_mixed (hG : PowConjRigid G) (hC : CommonPowers G) (hS : SimpleSystem S)
    (hH : HasPowersIn H) (hf : PowerExponentForm S H f) {α α' : G} (hαS : α ∈ S) (hα'S : α' ∈ S)
    {k k' : ℤ} (hk : k ≠ 0) (hk' : k' ≠ 0) (hα : α ^ k ∈ H) (hα' : α' ^ k' ∈ H)
    (hP : f ⟨α ^ k, hα⟩ = α ^ k) (hZ : f ⟨α' ^ k', hα'⟩ = 1) : False := by
  by_cases hsep : α' ≠ α ∧ α' ≠ α⁻¹
  · exact mixed_false_of_ne hG hC hS hf hαS hα'S hsep.1 hsep.2 hk hk' hα hα' hP hZ
  have hα'eq : α' = α ∨ α' = α⁻¹ := by tauto
  obtain ⟨β, hβS, hne, hne'⟩ := hS.exists_other α hαS
  obtain ⟨ℓ, hℓ, hβ⟩ := hH β
  have hne2 : α' ≠ β ∧ α' ≠ β⁻¹ := by
    rcases hα'eq with rfl | rfl
    · exact ⟨Ne.symm hne, ne_inv_symm hne'⟩
    · refine ⟨fun h => hne' h.symm, fun h => hne ?_⟩
      rw [← inv_inv β, ← h, inv_inv]
  rcases zero_or_id hG hC hS hH hf hβS hβ with h | h
  · exact mixed_false_of_ne hG hC hS hf hαS hβS hne hne' hk hℓ hα hβ hP h
  · exact mixed_false_of_ne hG hC hS hf hβS hα'S hne2.1 hne2.2 hℓ hk' hβ hα' h hZ

/-- **Chen–Salter, Lemma 3.3 and Corollary 3.4.** -/
theorem corollary_3_4 (hG : PowConjRigid G) (hC : CommonPowers G) (hS : SimpleSystem S)
    (hH : HasPowersIn H) (hf : PowerExponentForm S H f) :
    (∀ α ∈ S, ∀ (k : ℤ) (hk : α ^ k ∈ H), f ⟨α ^ k, hk⟩ = α ^ k) ∨
      (∀ α ∈ S, ∀ (k : ℤ) (hk : α ^ k ∈ H), f ⟨α ^ k, hk⟩ = 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨α, hαS, k, hα, hPne⟩, ⟨α', hα'S, k', hα', hZne⟩⟩ := hcon
  have hk : k ≠ 0 := by
    rintro rfl; exact hPne (by rw [mk_zpow_zero, map_one, zpow_zero])
  have hk' : k' ≠ 0 := by
    rintro rfl; exact hZne (by rw [mk_zpow_zero, map_one])
  have hZ : f ⟨α ^ k, hα⟩ = 1 := (zero_or_id hG hC hS hH hf hαS hα).resolve_right hPne
  have hP : f ⟨α' ^ k', hα'⟩ = α' ^ k' := (zero_or_id hG hC hS hH hf hα'S hα').resolve_left hZne
  exact not_mixed hG hC hS hH hf hα'S hαS hk' hk hα' hα hP hZ

/-- **Chen–Salter, Lemma 3.5.** In Case A, `f` is the inclusion of `H`. -/
theorem lemma_3_5 (hC : CommonPowers G) (hS : SimpleSystem S) (hSne : S.Nonempty)
    (hH : HasPowersIn H)
    (hA : ∀ α ∈ S, ∀ (k : ℤ) (hk : α ^ k ∈ H), f ⟨α ^ k, hk⟩ = α ^ k) (h : H) :
    f h = h := by
  obtain ⟨b, hb⟩ := h
  set x : G := b⁻¹ * f ⟨b, hb⟩ with hx
  -- `x` commutes with every power of a simple element lying in `H`.
  have hcomm : ∀ α ∈ S, ∀ (ℓ : ℤ) (hℓ : α ^ ℓ ∈ H), x * α ^ ℓ = α ^ ℓ * x := by
    intro α hαS ℓ hℓ
    have hmem : (b * α * b⁻¹) ^ ℓ ∈ H := by
      rw [conj_zpow]; exact H.mul_mem (H.mul_mem hb hℓ) (H.inv_mem hb)
    have h1 := hA _ (hS.conj_mem α hαS b) ℓ hmem
    have hsplit : (⟨(b * α * b⁻¹) ^ ℓ, hmem⟩ : H) =
        ⟨b, hb⟩ * ⟨α ^ ℓ, hℓ⟩ * (⟨b, hb⟩ : H)⁻¹ := by
      ext; simp [conj_zpow]
    rw [hsplit, map_mul, map_mul, map_inv, hA α hαS ℓ hℓ, conj_zpow] at h1
    rw [hx]
    calc b⁻¹ * f ⟨b, hb⟩ * α ^ ℓ
        = b⁻¹ * (f ⟨b, hb⟩ * α ^ ℓ * (f ⟨b, hb⟩)⁻¹) * f ⟨b, hb⟩ := by group
      _ = α ^ ℓ * (b⁻¹ * f ⟨b, hb⟩) := by rw [h1]; group
  by_contra hne
  have hx1 : x ≠ 1 := by
    rw [hx, Ne, inv_mul_eq_one]; exact fun h' => hne h'.symm
  obtain ⟨α, hαS⟩ := hSne
  obtain ⟨β, hβS, hβα, hβα'⟩ := hS.exists_other α hαS
  have hα1 : α ≠ 1 := fun h => hS.one_notMem (h ▸ hαS)
  have hβ1 : β ≠ 1 := fun h => hS.one_notMem (h ▸ hβS)
  obtain ⟨ℓ, hℓ0, hℓ⟩ := hH α
  obtain ⟨ℓ', hℓ'0, hℓ'⟩ := hH β
  have hαℓ : α ^ ℓ ≠ 1 := by rw [Ne, IsMulTorsionFree.zpow_eq_one_iff_right hα1]; exact hℓ0
  have hβℓ : β ^ ℓ' ≠ 1 := by rw [Ne, IsMulTorsionFree.zpow_eq_one_iff_right hβ1]; exact hℓ'0
  obtain ⟨c, d, hc, hd, hcd⟩ := hC x _ hx1 hαℓ (hcomm α hαS ℓ hℓ)
  obtain ⟨c', d', hc', hd', hcd'⟩ := hC x _ hx1 hβℓ (hcomm β hβS ℓ' hℓ')
  have hroot : β ^ (ℓ' * d' * c) = α ^ (ℓ * d * c') :=
    calc β ^ (ℓ' * d' * c) = ((β ^ ℓ') ^ d') ^ c := by rw [zpow_mul, zpow_mul]
      _ = (x ^ c') ^ c := by rw [hcd']
      _ = (x ^ c) ^ c' := by rw [← zpow_mul, ← zpow_mul, mul_comm c' c]
      _ = ((α ^ ℓ) ^ d) ^ c' := by rw [hcd]
      _ = α ^ (ℓ * d * c') := by rw [zpow_mul, zpow_mul]
  rcases hS.rootUnique β hβS α hαS _ _ (mul_ne_zero (mul_ne_zero hℓ'0 hd') hc)
      (mul_ne_zero (mul_ne_zero hℓ0 hd) hc') hroot with h' | h'
  · exact hβα h'
  · exact hβα' h'

end GroupApproximation.BirmanGenusThree.Section3
