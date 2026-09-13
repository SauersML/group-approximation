import GroupApproximation.GGT.HullLemma35Expansion
import GroupApproximation.GGT.HullSCUnconeSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: the two other sides of a triangle

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  For the triangle of chosen
geodesic words of `D` on `x`, `y`, `z`, `sidePoints D ex x y z` is the set of points of the guessed
paths from `x` to `z` and from `z` to `y`.  This module collects what the corner walk of
`GGT/HullLemma35Corner.lean` needs about it, at both corners of the side from `x` to `y`, given
`LetterNear D ex S T`: the points of the expansion of a component letter whose coset another side
meets (`SideConnected`) are within `T` of the other sides in `Γ(G, S)`.

* `vertex_mem_sidePoints_left`, `vertex_mem_sidePoints_right`,
  `vertex_revWord_mem_sidePoints_right` — the vertices of the other sides are side points;
* `exit_near_of_connected`, `entrance_near_of_connected` — the ends of a connected letter;
* `side_left`, `side_right` — the side hypothesis of `corner_near` at the corners `x` and `y`.

It adapts `GGT/HullSCUnconeSides.lean`.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.Uncone (exists_comp_of_isCompOf exists_isComp_of_isComp_revWord
  span_mem_relBall_of_noComp avoidsCosetFrom_of_noComp noComp_of_avoidsCosetFrom)

universe u w

section Sides

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The points of the guessed paths of the other two sides** of the triangle on `x`, `y`, `z`. -/
def sidePoints (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) (x y z : G) : Set G :=
  {p | ∃ n ≤ guessLen D ex x z, guessPath D ex x z n = p} ∪
    {p | ∃ n ≤ guessLen D ex z y, guessPath D ex z y n = p}

/-- **The `t`-th letter of the side from `x` to `y` is connected to another side**: one of the
other two sides has a component on its coset. -/
def SideConnected (D : RelGenSet G Λ) (x y z : G) (lam : Λ) (t : ℕ) : Prop :=
  (∃ i₂ k₂ : ℕ, IsComp lam (geodWord D x z) i₂ k₂ ∧
      (QuotientGroup.mk (vertex x (geodWord D x z) i₂) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex x (geodWord D x y) t)) ∨
    (∃ i₃ k₃ : ℕ, IsComp lam (geodWord D z y) i₃ k₃ ∧
      (QuotientGroup.mk (vertex z (geodWord D z y) i₃) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex x (geodWord D x y) t))

/-- **Connected letters are near the other sides**: every point of the guessed path inside the
expansion of a connected component letter is within `T` of the side points in `Γ(G, S)`. -/
def LetterNear (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) (S : Set G) (T : ℕ) : Prop :=
  ∀ (x y z : G) (t : ℕ) (ht : t < (geodWord D x y).length) (lam : Λ) (e : G),
    (geodWord D x y)[t]'ht = RelLetter.comp lam e → SideConnected D x y z lam t →
      ∀ s ≤ (ex ((geodWord D x y)[t]'ht)).length, ∃ p ∈ sidePoints D ex x y z,
        wordDist S (guessPath D ex x y ((expWord ex ((geodWord D x y).take t)).length + s)) p ≤ T

/-- At the end of the expansion of a letter the guessed path is at the next vertex. -/
theorem guessPath_letter_end (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y : G) {t : ℕ}
    (ht : t < (geodWord D x y).length) :
    guessPath D ex x y
        ((expWord ex ((geodWord D x y).take t)).length + (ex ((geodWord D x y)[t]'ht)).length)
      = vertex x (geodWord D x y) (t + 1) := by
  rw [guessPath_in_letter D ex hprod x y ht le_rfl, List.take_length,
    hprod _ ((geodWord_spec D x y).1 _ (List.getElem_mem ht)), vertex_succ _ x t ht]

theorem vertex_mem_sidePoints_left (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y z : G) (i : ℕ) :
    vertex x (geodWord D x z) i ∈ sidePoints D ex x y z := by
  rw [← guessPath_at_letter D ex hprod x z i]
  exact Or.inl ⟨_, length_expWord_take_le ex (geodWord D x z) i, rfl⟩

theorem vertex_mem_sidePoints_right (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y z : G) (i : ℕ) :
    vertex z (geodWord D z y) i ∈ sidePoints D ex x y z := by
  rw [← guessPath_at_letter D ex hprod z y i]
  exact Or.inr ⟨_, length_expWord_take_le ex (geodWord D z y) i, rfl⟩

theorem vertex_revWord_mem_sidePoints_right (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y z : G) {i : ℕ}
    (hi : i ≤ (revWord (geodWord D z y)).length) :
    vertex y (revWord (geodWord D z y)) i ∈ sidePoints D ex x y z := by
  have hlen : (revWord (geodWord D z y)).length = (geodWord D z y).length := by simp [revWord]
  have h := vertex_revWord_of_end (geodWord D z y) z ((geodWord D z y).length - i)
  rw [(geodWord_spec D z y).2.1,
    show (geodWord D z y).length - ((geodWord D z y).length - i) = i by omega] at h
  rw [h]
  exact vertex_mem_sidePoints_right D ex hprod x y z _

/-- **The exit of a connected component letter is near the other sides.** -/
theorem exit_near_of_connected (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) {S : Set G} {T : ℕ}
    (hnear : LetterNear D ex S T) (x y z : G) {t : ℕ} (ht : t < (geodWord D x y).length)
    {lam : Λ} {e : G} (hletter : (geodWord D x y)[t]'ht = RelLetter.comp lam e)
    (hconn : SideConnected D x y z lam t) :
    ∃ p ∈ sidePoints D ex x y z, wordDist S (vertex x (geodWord D x y) (t + 1)) p ≤ T := by
  rw [← guessPath_letter_end D ex hprod x y ht]
  exact hnear x y z t ht lam e hletter hconn _ le_rfl

/-- **The entrance of a connected component letter is near the other sides.** -/
theorem entrance_near_of_connected (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) {S : Set G} {T : ℕ}
    (hnear : LetterNear D ex S T) (x y z : G) {t : ℕ} (ht : t < (geodWord D x y).length)
    {lam : Λ} {e : G} (hletter : (geodWord D x y)[t]'ht = RelLetter.comp lam e)
    (hconn : SideConnected D x y z lam t) :
    ∃ p ∈ sidePoints D ex x y z, wordDist S (vertex x (geodWord D x y) t) p ≤ T := by
  have hpt : guessPath D ex x y ((expWord ex ((geodWord D x y).take t)).length + 0)
      = vertex x (geodWord D x y) t := by
    rw [add_zero]
    exact guessPath_at_letter D ex hprod x y t
  rw [← hpt]
  exact hnear x y z t ht lam e hletter hconn 0 (Nat.zero_le _)

/-- **The side hypothesis of the corner walk at the corner `x`.** -/
theorem side_left (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {S : Set G} (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val)
    (hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam Dc → wordDist S A B ≤ T)
    (hnear : LetterNear D ex S T) (x y z : G) (k : ℕ) :
    ∀ (lam : Λ) (t : ℕ), t < k → IsComp lam (geodWord D x y) t (t + 1) →
      (∃ p ∈ sidePoints D ex x y z, wordDist S (vertex x (geodWord D x y) (t + 1)) p ≤ T) ∨
        (wordDist S (vertex x (geodWord D x y) t) (vertex x (geodWord D x y) (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp lam (geodWord D x z) i' k' →
            (QuotientGroup.mk (vertex x (geodWord D x z) i') : G ⧸ D.fam lam)
              ≠ QuotientGroup.mk (vertex x (geodWord D x y) t)) := by
  intro lam t _ hc
  have hc2 := hc.2.1
  have ht : t < (geodWord D x y).length := by omega
  obtain ⟨e, he⟩ := exists_comp_of_isCompOf (hc.2.2.1 t le_rfl (by omega) ht)
  by_cases hconn : SideConnected D x y z lam t
  · exact Or.inl (exit_near_of_connected D ex hprod hnear x y z ht he hconn)
  · have hno₂ : ∀ i' k' : ℕ, IsComp lam (geodWord D x z) i' k' →
        (QuotientGroup.mk (vertex x (geodWord D x z) i') : G ⧸ D.fam lam)
          ≠ QuotientGroup.mk (vertex x (geodWord D x y) t) :=
      fun i' k' hc' hcos => hconn (Or.inl ⟨i', k', hc', hcos⟩)
    have hno₃ : ∀ i' k' : ℕ, IsComp lam (geodWord D z y) i' k' →
        (QuotientGroup.mk (vertex z (geodWord D z y) i') : G ⧸ D.fam lam)
          ≠ QuotientGroup.mk (vertex x (geodWord D x y) t) :=
      fun i' k' hc' hcos => hconn (Or.inr ⟨i', k', hc', hcos⟩)
    have h0 := span_mem_relBall_of_noComp D lam hsymm hbnd hDc (geodWord_spec D x y)
      (geodWord_spec D x z) (geodWord_spec D z y) hc hno₂ hno₃
    exact Or.inr ⟨hball lam _ _ h0, hno₂⟩

/-- **The side hypothesis of the corner walk at the corner `y`**, on the reversed words. -/
theorem side_right (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val)
    (hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam Dc → wordDist S A B ≤ T)
    (hnear : LetterNear D ex S T) (x y z : G) (k : ℕ) :
    ∀ (lam : Λ) (t : ℕ), t < k → IsComp lam (revWord (geodWord D x y)) t (t + 1) →
      (∃ p ∈ sidePoints D ex x y z,
          wordDist S (vertex y (revWord (geodWord D x y)) (t + 1)) p ≤ T) ∨
        (wordDist S (vertex y (revWord (geodWord D x y)) t)
            (vertex y (revWord (geodWord D x y)) (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp lam (revWord (geodWord D z y)) i' k' →
            (QuotientGroup.mk (vertex y (revWord (geodWord D z y)) i') : G ⧸ D.fam lam)
              ≠ QuotientGroup.mk (vertex y (revWord (geodWord D x y)) t)) := by
  intro lam t _ hc
  have hw₁ := geodWord_spec D x y
  have hw₃ := geodWord_spec D z y
  obtain ⟨t', htt, hcW⟩ := exists_isComp_of_isComp_revWord D hw₁ hc
  have hc2 := hcW.2.1
  have ht' : t' < (geodWord D x y).length := by omega
  obtain ⟨e, he⟩ := exists_comp_of_isCompOf (hcW.2.2.1 t' le_rfl (by omega) ht')
  have hv₁ : vertex y (revWord (geodWord D x y)) (t + 1) = vertex x (geodWord D x y) t' := by
    have h := vertex_revWord_of_end (geodWord D x y) x t'
    rwa [hw₁.2.1, show (geodWord D x y).length - t' = t + 1 by omega] at h
  have hv₀ : vertex y (revWord (geodWord D x y)) t = vertex x (geodWord D x y) (t' + 1) := by
    have h := vertex_revWord_of_end (geodWord D x y) x (t' + 1)
    rwa [hw₁.2.1, show (geodWord D x y).length - (t' + 1) = t by omega] at h
  rw [hv₁, hv₀]
  have hcos := mk_vertex_eq_of_isComp D x hw₁.1 hcW
  by_cases hconn : SideConnected D x y z lam t'
  · exact Or.inl (entrance_near_of_connected D ex hprod hnear x y z ht' he hconn)
  · have hno₂ : ∀ i' k' : ℕ, IsComp lam (geodWord D x z) i' k' →
        (QuotientGroup.mk (vertex x (geodWord D x z) i') : G ⧸ D.fam lam)
          ≠ QuotientGroup.mk (vertex x (geodWord D x y) t') :=
      fun i' k' hc' hcos' => hconn (Or.inl ⟨i', k', hc', hcos'⟩)
    have hno₃ : ∀ i' k' : ℕ, IsComp lam (geodWord D z y) i' k' →
        (QuotientGroup.mk (vertex z (geodWord D z y) i') : G ⧸ D.fam lam)
          ≠ QuotientGroup.mk (vertex x (geodWord D x y) t') :=
      fun i' k' hc' hcos' => hconn (Or.inr ⟨i', k', hc', hcos'⟩)
    have h0 := span_mem_relBall_of_noComp D lam hsymm hbnd hDc hw₁
      (geodWord_spec D x z) hw₃ hcW hno₂ hno₃
    have hd := hball lam _ _ h0
    have hav := (avoidsCosetFrom_of_noComp D hw₃.1 hno₃).revWord hw₃.1
    rw [hw₃.2.1] at hav
    refine Or.inr ⟨?_, ?_⟩
    · rw [wordDist_comm hS]
      exact hd
    · rw [← hcos]
      exact noComp_of_avoidsCosetFrom hav

end Sides

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.guessPath_letter_end
#audit_axioms GroupApproximation.GGT.HullLemma35.vertex_mem_sidePoints_left
#audit_axioms GroupApproximation.GGT.HullLemma35.vertex_revWord_mem_sidePoints_right
#audit_axioms GroupApproximation.GGT.HullLemma35.exit_near_of_connected
#audit_axioms GroupApproximation.GGT.HullLemma35.entrance_near_of_connected
#audit_axioms GroupApproximation.GGT.HullLemma35.side_left
#audit_axioms GroupApproximation.GGT.HullLemma35.side_right
