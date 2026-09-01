import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyFourWay

/-! Admissibility utilities shared by the exact relator consumers. -/

namespace GroupApproximation
namespace HullSC

universe u v

variable {G : Type u} [Group G] {Λ : Type v}

theorem isLetter_relWordInv (D : GGT.RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {a : GGT.RelLetter G Λ}
    (hlet : D.IsLetter a) : D.IsLetter (RelWord.inv a) := by
  cases a with
  | base x => exact hsymm x hlet
  | comp lam h => exact inv_mem hlet

theorem isAdmissible_rotate {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} (h : RelWord.IsAdmissible D v) (n : ℕ) :
    RelWord.IsAdmissible D (v.rotate n) :=
  fun a ha => h a (List.mem_rotate.mp ha)

theorem isAdmissible_revInv {D : GGT.RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v : List (GGT.RelLetter G Λ)}
    (h : RelWord.IsAdmissible D v) :
    RelWord.IsAdmissible D (RelWord.revInv v) := by
  intro a ha
  rw [RelWord.revInv, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact isLetter_relWordInv D hsymm (h b hb)

theorem isAdmissible_sym {D : GGT.RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v w : List (GGT.RelLetter G Λ)}
    (hw : RelWord.Sym v w) (h : RelWord.IsAdmissible D v) :
    RelWord.IsAdmissible D w := by
  induction hw with
  | base => exact h
  | rot n _hs ih => exact isAdmissible_rotate ih n
  | inv _hs ih => exact isAdmissible_revInv hsymm ih

theorem isAdmissible_revWord {D : GGT.RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v : List (GGT.RelLetter G Λ)}
    (h : RelWord.IsAdmissible D v) :
    RelWord.IsAdmissible D (GGT.OsinComponents.revWord v) := by
  intro a ha
  rw [GGT.OsinComponents.revWord, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact GGT.OsinComponents.isLetter_invLetter D hsymm (h b hb)

theorem isLetter_of_mem_blockWord {D : GGT.RelGenSet G Bool} {a : Bool → G}
    (ha : ∀ b : Bool, a b ∈ D.fam b) :
    ∀ (s : Bool) (ms : List ℕ), ∀ x ∈ blockWord (a false) (a true) s ms,
      D.IsLetter x := by
  intro s ms
  induction ms generalizing s with
  | nil =>
      intro x hx
      rw [blockWord_nil] at hx
      cases hx
  | cons m t ih =>
      intro x hx
      rw [blockWord_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · show (if s then a true else a false) ^ m ∈ D.fam s
        rw [ite_apply_eq a s]
        exact pow_mem (ha s) m
      · exact ih (!s) x hx

theorem isAdmissible_relatorWord₂ {D : GGT.RelGenSet G Bool} {p : List G}
    (hp : ∀ g ∈ p, g ∈ D.base) {a : Bool → G}
    (ha : ∀ b : Bool, a b ∈ D.fam b) (ms : List ℕ) :
    RelWord.IsAdmissible D (relatorWord₂ p (a false) (a true) ms) := by
  intro x hx
  rw [relatorWord₂, List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hp g hg
  · exact isLetter_of_mem_blockWord ha false ms x hx

end HullSC
end GroupApproximation
