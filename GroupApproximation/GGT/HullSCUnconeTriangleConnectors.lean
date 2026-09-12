import GroupApproximation.GGT.HullSCUnconeCosetAvoidance
import GroupApproximation.GGT.OsinTheorem54SepEntranceConnector
import GroupApproximation.GGT.OsinTheorem54SepLemma45
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 4: components of a triangle on a common coset

Let `x`, `y`, `z` be joined by geodesic words `w₁ : x → y`, `w₂ : x → z`, `w₃ : z → y`, and let a
`λ`-component `c` of `w₁` lie on a coset `K` of `H_λ`.  Its entrance `c₋` and exit `c₊` are compared
with the components of the other two sides on `K`, in the `d̂_λ` metric:

* `exitConnector_mem_relBall` — two geodesics ending at a common point exit a common coset nearby
  (the entrance connector of Osin's Lemma 4.6 on the reversed words);
* `exitEntranceConnector_mem_relBall` — at the common vertex of two consecutive sides, the exit of
  the first and the entrance of the second are close;
* `exitConnector_of_noComp` — if `w₂` penetrates `K` and `w₃` does not, the exits of `c` and of the
  component of `w₂` are close (a closing jump across `w₁` after `c`, `w₃` reversed, and `w₂` after
  its component, reversed);
* `entranceConnector_of_noComp` — if `w₃` penetrates `K` and `w₂` does not, the entrances are close;
* `span_mem_relBall_of_noComp` — if neither does, the span of `c` is short (Osin's Lemma 4.5).

Every constant here is the isolated-component constant `C` of Proposition 4.2 or `Dc ≥ 4C`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

namespace Uncone

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A suffix of a geodesic word is a geodesic word**, from the vertex it starts at. -/
theorem geodesicWord_drop (D : RelGenSet G Λ) {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {k : ℕ} (hk : k ≤ w.length) :
    IsGeodesicWord D (vertex f w k) g (w.drop k) := by
  have h := isGeodesicWord_segment D hw hk le_rfl
  rw [List.take_of_length_le (by simp), IsGeodesicWord.vertex_length_eq hw] at h
  exact h

/-- **Two geodesics ending at a common point exit a common coset nearby.** -/
theorem exitConnector_mem_relBall (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {f f' g : G} {p q : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D f g p) (hq : IsGeodesicWord D f' g q) {i i' j j' : ℕ}
    (hpi : IsComp lam p i i') (hqj : IsComp lam q j j')
    (hcos : (QuotientGroup.mk (vertex f p i) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex f' q j)) :
    (vertex f p i')⁻¹ * vertex f' q j' ∈ D.relBall lam Dc := by
  have hp' := isGeodesicWord_revWord D hsymm hp
  have hq' := isGeodesicWord_revWord D hsymm hq
  have hpi' := isComp_revWord lam p hpi
  have hqj' := isComp_revWord lam q hqj
  have hvp : vertex g (revWord p) (p.length - i') = vertex f p i' := by
    have h := vertex_revWord_of_end p f i'
    rwa [hp.2.1] at h
  have hvq : vertex g (revWord q) (q.length - j') = vertex f' q j' := by
    have h := vertex_revWord_of_end q f' j'
    rwa [hq.2.1] at h
  have hcos' : (QuotientGroup.mk (vertex g (revWord p) (p.length - i')) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex g (revWord q) (q.length - j')) := by
    rw [hvp, hvq, ← mk_vertex_eq_of_isComp D f hp.1 hpi, ← mk_vertex_eq_of_isComp D f' hq.1 hqj]
    exact hcos
  have h := entranceConnector_mem_relBall_of_bound D lam hsymm hbnd hDc hp' hq' hpi' hqj' hcos'
  rwa [hvp, hvq] at h

/-- **At the common vertex of two consecutive geodesic sides, the exit of the first and the
entrance of the second into a common coset are close.** -/
theorem exitEntranceConnector_mem_relBall (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {f g h : G} {p q : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D f g p) (hq : IsGeodesicWord D g h q) {i i' j j' : ℕ}
    (hpi : IsComp lam p i i') (hqj : IsComp lam q j j')
    (hcos : (QuotientGroup.mk (vertex f p i) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex g q j)) :
    (vertex f p i')⁻¹ * vertex g q j ∈ D.relBall lam Dc := by
  have hp' := isGeodesicWord_revWord D hsymm hp
  have hpi' := isComp_revWord lam p hpi
  have hvp : vertex g (revWord p) (p.length - i') = vertex f p i' := by
    have h0 := vertex_revWord_of_end p f i'
    rwa [hp.2.1] at h0
  have hcos' : (QuotientGroup.mk (vertex g (revWord p) (p.length - i')) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex g q j) := by
    rw [hvp, ← mk_vertex_eq_of_isComp D f hp.1 hpi]
    exact hcos
  have h0 := entranceConnector_mem_relBall_of_bound D lam hsymm hbnd hDc hp' hq hpi' hqj hcos'
  rwa [hvp] at h0

/-- **If the second side penetrates the coset and the third does not, the exits are close.** -/
theorem exitConnector_of_noComp (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    {x y z : G} {w₁ w₂ w₃ : List (RelLetter G Λ)}
    (hw₁ : IsGeodesicWord D x y w₁) (hw₂ : IsGeodesicWord D x z w₂)
    (hw₃ : IsGeodesicWord D z y w₃) {i₁ k₁ i₂ k₂ : ℕ}
    (hc₁ : IsComp lam w₁ i₁ k₁) (hc₂ : IsComp lam w₂ i₂ k₂)
    (hcos : (QuotientGroup.mk (vertex x w₁ i₁) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex x w₂ i₂))
    (hno : ∀ i k : ℕ, IsComp lam w₃ i k →
      (QuotientGroup.mk (vertex z w₃ i) : G ⧸ D.fam lam) ≠ QuotientGroup.mk (vertex x w₁ i₁)) :
    (vertex x w₂ k₂)⁻¹ * vertex x w₁ k₁ ∈ D.relBall lam (C * 4) := by
  have hKa : (QuotientGroup.mk (vertex x w₁ i₁) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex x w₁ k₁) := mk_vertex_eq_of_isComp D x hw₁.1 hc₁
  have hk₁ : k₁ ≤ w₁.length := hc₁.2.1
  have hk₂ : k₂ ≤ w₂.length := hc₂.2.1
  have hp := geodesicWord_drop D hw₁ hk₁
  have hap : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ k₁)) (vertex x w₁ k₁)
      (w₁.drop k₁) := by
    have h0 := avoidsCosetFrom_drop_of_isComp D hw₁ hc₁
    rwa [hKa] at h0
  have hq := isGeodesicWord_revWord D hsymm hw₃
  have haq : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ k₁)) y (revWord w₃) := by
    have h0 : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ k₁)) z w₃ :=
      avoidsCosetFrom_of_noComp D hw₃.1 (fun i k hc => by
        rw [← hKa]
        exact hno i k hc)
    have h1 := h0.revWord hw₃.1
    rwa [hw₃.2.1] at h1
  have hd₂ := geodesicWord_drop D hw₂ hk₂
  have hr := isGeodesicWord_revWord D hsymm hd₂
  have har : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ k₁)) z
      (revWord (w₂.drop k₂)) := by
    have h0 := avoidsCosetFrom_drop_of_isComp D hw₂ hc₂
    have hK2 : (QuotientGroup.mk (vertex x w₂ i₂) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex x w₁ k₁) := by
      rw [← hcos, hKa]
    rw [hK2] at h0
    have h1 := h0.revWord (fun b hb => hw₂.1 b (List.drop_subset k₂ w₂ hb))
    rwa [hd₂.2.1] at h1
  have hcoset : (QuotientGroup.mk (vertex x w₂ k₂) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex x w₁ k₁) := by
    rw [← mk_vertex_eq_of_isComp D x hw₂.1 hc₂, ← hcos, hKa]
  exact closingJump_located D hsymm hbnd lam hp hq hr hcoset hap haq har

/-- **If the third side penetrates the coset and the second does not, the entrances are close.** -/
theorem entranceConnector_of_noComp (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    {x y z : G} {w₁ w₂ w₃ : List (RelLetter G Λ)}
    (hw₁ : IsGeodesicWord D x y w₁) (hw₂ : IsGeodesicWord D x z w₂)
    (hw₃ : IsGeodesicWord D z y w₃) {i₁ k₁ i₃ k₃ : ℕ}
    (hc₁ : IsComp lam w₁ i₁ k₁) (hc₃ : IsComp lam w₃ i₃ k₃)
    (hcos : (QuotientGroup.mk (vertex x w₁ i₁) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex z w₃ i₃))
    (hno : ∀ i k : ℕ, IsComp lam w₂ i k →
      (QuotientGroup.mk (vertex x w₂ i) : G ⧸ D.fam lam) ≠ QuotientGroup.mk (vertex x w₁ i₁)) :
    (vertex z w₃ i₃)⁻¹ * vertex x w₁ i₁ ∈ D.relBall lam (C * 4) := by
  have hi₁ : i₁ ≤ w₁.length := le_of_lt (lt_of_lt_of_le hc₁.1 hc₁.2.1)
  have hi₃ : i₃ ≤ w₃.length := le_of_lt (lt_of_lt_of_le hc₃.1 hc₃.2.1)
  have ht₁ := isGeodesicWord_take D hw₁ hi₁
  have hp := isGeodesicWord_revWord D hsymm ht₁
  have hap : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ i₁)) (vertex x w₁ i₁)
      (revWord (w₁.take i₁)) := by
    have h0 := (avoidsCosetFrom_take_of_isComp D hw₁ hc₁).revWord
      (fun b hb => hw₁.1 b (List.take_subset i₁ w₁ hb))
    rwa [ht₁.2.1] at h0
  have haq : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ i₁)) x w₂ :=
    avoidsCosetFrom_of_noComp D hw₂.1 hno
  have hr := isGeodesicWord_take D hw₃ hi₃
  have har : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex x w₁ i₁)) z (w₃.take i₃) := by
    have h0 := avoidsCosetFrom_take_of_isComp D hw₃ hc₃
    rwa [← hcos] at h0
  exact closingJump_located D hsymm hbnd lam hp hw₂ hr hcos.symm hap haq har

/-- **If neither other side penetrates the coset, the component has a short span**: a deep component
would make its coset separate `x` from `y`, and Osin's Lemma 4.5 then puts a component of `w₂` or of
`w₃` on it. -/
theorem span_mem_relBall_of_noComp (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {x y z : G} {w₁ w₂ w₃ : List (RelLetter G Λ)}
    (hw₁ : IsGeodesicWord D x y w₁) (hw₂ : IsGeodesicWord D x z w₂)
    (hw₃ : IsGeodesicWord D z y w₃) {i₁ k₁ : ℕ} (hc₁ : IsComp lam w₁ i₁ k₁)
    (hno₂ : ∀ i k : ℕ, IsComp lam w₂ i k →
      (QuotientGroup.mk (vertex x w₂ i) : G ⧸ D.fam lam) ≠ QuotientGroup.mk (vertex x w₁ i₁))
    (hno₃ : ∀ i k : ℕ, IsComp lam w₃ i k →
      (QuotientGroup.mk (vertex z w₃ i) : G ⧸ D.fam lam) ≠ QuotientGroup.mk (vertex x w₁ i₁)) :
    (vertex x w₁ i₁)⁻¹ * vertex x w₁ k₁ ∈ D.relBall lam Dc := by
  by_contra hdeep
  have hsep : (QuotientGroup.mk (vertex x w₁ i₁) : G ⧸ D.fam lam) ∈ sepSet D lam Dc x y :=
    ⟨w₁, i₁, k₁, hw₁, ⟨hc₁, hdeep⟩, rfl⟩
  rcases penetrates_of_mem_sepSet D lam hsymm hbnd hDc hw₂ hw₃ hsep with
      ⟨m, n, hmn, hm⟩ | ⟨m, n, hmn, hm⟩
  · exact hno₂ m n hmn hm
  · exact hno₃ m n hmn hm

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.geodesicWord_drop
#audit_axioms GroupApproximation.GGT.Uncone.exitConnector_mem_relBall
#audit_axioms GroupApproximation.GGT.Uncone.exitEntranceConnector_mem_relBall
#audit_axioms GroupApproximation.GGT.Uncone.exitConnector_of_noComp
#audit_axioms GroupApproximation.GGT.Uncone.entranceConnector_of_noComp
#audit_axioms GroupApproximation.GGT.Uncone.span_mem_relBall_of_noComp
