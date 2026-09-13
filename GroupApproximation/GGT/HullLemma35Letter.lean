import GroupApproximation.GGT.HullLemma35PieceSides
import GroupApproximation.GGT.HullSCUnconeLemmaA
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: the expansion of a connected letter

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  This module proves
`LetterNear` for `properRelGenSet D` and the expansion `transEx D E`
(`letterNear_properRelGenSet`).  A component letter of the side from `x` to `y` on the coset
`a H_λ` that another side meets closes, through the triangle connectors, a polygon in
`Γ(H_λ, E λ)`:

* `nearBetween_quad_left` — only the side from `x` to `z` meets the coset;
* `nearBetween_quad_right` — only the side from `z` to `y` meets it;
* `nearBetween_hexagon_both` — both do.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.Uncone (isComp_succ_of_isCompOf_geodesic exitConnector_mem_relBall
  exitEntranceConnector_mem_relBall exitConnector_of_noComp entranceConnector_of_noComp)

universe u v w

section Letter

variable {G : Type u} [Group G] {Λ : Type v} {M : Λ → Type w}

/-- **Only the side from `x` to `z` meets the coset**: a quadrilateral. -/
theorem nearBetween_quad_left (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {C Dc Tb δ : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon (properRelGenSet D) 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated (properRelGenSet D).fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ (properRelGenSet D).relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hTb : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam Dc → (pieceWord D E lam e).length ≤ Tb)
    {lam : Λ} (hδ : Hyperbolic.IsFourPointHyperbolic (E lam).alphabet.carrier δ) (x y z : G)
    {t : ℕ} (hc₁ : IsComp lam (geodWord (properRelGenSet D) x y) t (t + 1))
    (h0 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) t ∈ D.fam lam)
    (h1 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) (t + 1) ∈ D.fam lam)
    {i₂ k₂ : ℕ} (hc₂ : IsComp lam (geodWord (properRelGenSet D) x z) i₂ k₂)
    (hcos₂ : (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t) :
        G ⧸ (properRelGenSet D).fam lam)
      = QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x z) i₂))
    (hno₃ : ∀ i k : ℕ, IsComp lam (geodWord (properRelGenSet D) z y) i k →
      (QuotientGroup.mk (vertex z (geodWord (properRelGenSet D) z y) i) :
          G ⧸ (properRelGenSet D).fam lam)
        ≠ QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t)) :
    NearBetween (E lam).alphabet.carrier
      (cosetPoints (D.fam lam) (vertex x (geodWord (properRelGenSet D) x y) t)
        (sidePoints (properRelGenSet D) (transEx D E) x y z))
      (8 * δ + (2 * δ + Tb)) ⟨_, h0⟩ ⟨_, h1⟩ := by
  have hw₁ := geodWord_spec (properRelGenSet D) x y
  have hw₂ := geodWord_spec (properRelGenSet D) x z
  have hw₃ := geodWord_spec (properRelGenSet D) z y
  have hprod : ∀ r : RelLetter G Λ, (properRelGenSet D).IsLetter r →
      (transEx D E r).prod = r.val := fun r _ => transEx_prod D E r
  have hb₂ : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x z) i₂ ∈ D.fam lam := QuotientGroup.eq.mp hcos₂
  have hc₂' : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x z) k₂ ∈ D.fam lam :=
    QuotientGroup.eq.mp (hcos₂.trans (mk_vertex_eq_of_isComp (properRelGenSet D) x hw₂.1 hc₂))
  refine nearBetween_quad (E lam).alphabet.symmetricGenerating hδ (X₂ := ⟨_, hc₂'⟩)
    (X₃ := ⟨_, hb₂⟩) ?_ ?_ ?_ ?_ ?_
  · rw [wordDist_comm (E lam).alphabet.symmetricGenerating]
    exact wordDist_cosetCoord_le D E (hTb lam) _ hc₂' h1
      (relBall_mono_radius (properRelGenSet D) lam hDc
        (exitConnector_of_noComp (properRelGenSet D) lam (properRelGenSet_base_inv D) hbnd
          hw₁ hw₂ hw₃ hc₁ hc₂ hcos₂ hno₃))
  · exact mem_cosetPoints_of_mem _ hc₂'
      (vertex_mem_sidePoints_left (properRelGenSet D) (transEx D E) hprod x y z k₂)
  · exact cosetPoints_side D E (Q := sidePoints (properRelGenSet D) (transEx D E) x y z) x z
      (fun n hn => Or.inl ⟨n, hn, rfl⟩) hc₂ _ hb₂ hc₂'
  · exact wordDist_cosetCoord_le D E (hTb lam) _ h0 hb₂
      (entranceConnector_mem_relBall_of_bound (properRelGenSet D) lam
        (properRelGenSet_base_inv D) hbnd hDc hw₁ hw₂ hc₁ hc₂ hcos₂)
  · exact mem_cosetPoints_of_mem _ hb₂
      (vertex_mem_sidePoints_left (properRelGenSet D) (transEx D E) hprod x y z i₂)

/-- **Only the side from `z` to `y` meets the coset**: a quadrilateral. -/
theorem nearBetween_quad_right (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {C Dc Tb δ : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon (properRelGenSet D) 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated (properRelGenSet D).fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ (properRelGenSet D).relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hTb : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam Dc → (pieceWord D E lam e).length ≤ Tb)
    {lam : Λ} (hδ : Hyperbolic.IsFourPointHyperbolic (E lam).alphabet.carrier δ) (x y z : G)
    {t : ℕ} (hc₁ : IsComp lam (geodWord (properRelGenSet D) x y) t (t + 1))
    (h0 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) t ∈ D.fam lam)
    (h1 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) (t + 1) ∈ D.fam lam)
    {i₃ k₃ : ℕ} (hc₃ : IsComp lam (geodWord (properRelGenSet D) z y) i₃ k₃)
    (hcos₃ : (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t) :
        G ⧸ (properRelGenSet D).fam lam)
      = QuotientGroup.mk (vertex z (geodWord (properRelGenSet D) z y) i₃))
    (hno₂ : ∀ i k : ℕ, IsComp lam (geodWord (properRelGenSet D) x z) i k →
      (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x z) i) :
          G ⧸ (properRelGenSet D).fam lam)
        ≠ QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t)) :
    NearBetween (E lam).alphabet.carrier
      (cosetPoints (D.fam lam) (vertex x (geodWord (properRelGenSet D) x y) t)
        (sidePoints (properRelGenSet D) (transEx D E) x y z))
      (8 * δ + (2 * δ + Tb)) ⟨_, h0⟩ ⟨_, h1⟩ := by
  have hw₁ := geodWord_spec (properRelGenSet D) x y
  have hw₂ := geodWord_spec (properRelGenSet D) x z
  have hw₃ := geodWord_spec (properRelGenSet D) z y
  have hprod : ∀ r : RelLetter G Λ, (properRelGenSet D).IsLetter r →
      (transEx D E r).prod = r.val := fun r _ => transEx_prod D E r
  have hb₃ : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex z (geodWord (properRelGenSet D) z y) i₃ ∈ D.fam lam := QuotientGroup.eq.mp hcos₃
  have hc₃' : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex z (geodWord (properRelGenSet D) z y) k₃ ∈ D.fam lam :=
    QuotientGroup.eq.mp (hcos₃.trans (mk_vertex_eq_of_isComp (properRelGenSet D) z hw₃.1 hc₃))
  refine nearBetween_quad (E lam).alphabet.symmetricGenerating hδ (X₂ := ⟨_, hc₃'⟩)
    (X₃ := ⟨_, hb₃⟩) ?_ ?_ ?_ ?_ ?_
  · exact wordDist_cosetCoord_le D E (hTb lam) _ h1 hc₃'
      (exitConnector_mem_relBall (properRelGenSet D) lam (properRelGenSet_base_inv D) hbnd hDc
        hw₁ hw₃ hc₁ hc₃ hcos₃)
  · exact mem_cosetPoints_of_mem _ hc₃'
      (vertex_mem_sidePoints_right (properRelGenSet D) (transEx D E) hprod x y z k₃)
  · exact cosetPoints_side D E (Q := sidePoints (properRelGenSet D) (transEx D E) x y z) z y
      (fun n hn => Or.inr ⟨n, hn, rfl⟩) hc₃ _ hb₃ hc₃'
  · rw [wordDist_comm (E lam).alphabet.symmetricGenerating]
    exact wordDist_cosetCoord_le D E (hTb lam) _ hb₃ h0
      (relBall_mono_radius (properRelGenSet D) lam hDc
        (entranceConnector_of_noComp (properRelGenSet D) lam (properRelGenSet_base_inv D) hbnd
          hw₁ hw₂ hw₃ hc₁ hc₃ hcos₃ hno₂))
  · exact mem_cosetPoints_of_mem _ hb₃
      (vertex_mem_sidePoints_right (properRelGenSet D) (transEx D E) hprod x y z i₃)

/-- **Both other sides meet the coset**: a hexagon. -/
theorem nearBetween_hexagon_both (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {C Dc Tb δ : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon (properRelGenSet D) 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated (properRelGenSet D).fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ (properRelGenSet D).relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hTb : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam Dc → (pieceWord D E lam e).length ≤ Tb)
    {lam : Λ} (hδ : Hyperbolic.IsFourPointHyperbolic (E lam).alphabet.carrier δ) (x y z : G)
    {t : ℕ} (hc₁ : IsComp lam (geodWord (properRelGenSet D) x y) t (t + 1))
    (h0 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) t ∈ D.fam lam)
    (h1 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) (t + 1) ∈ D.fam lam)
    {i₂ k₂ : ℕ} (hc₂ : IsComp lam (geodWord (properRelGenSet D) x z) i₂ k₂)
    (hcos₂ : (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t) :
        G ⧸ (properRelGenSet D).fam lam)
      = QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x z) i₂))
    {i₃ k₃ : ℕ} (hc₃ : IsComp lam (geodWord (properRelGenSet D) z y) i₃ k₃)
    (hcos₃ : (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t) :
        G ⧸ (properRelGenSet D).fam lam)
      = QuotientGroup.mk (vertex z (geodWord (properRelGenSet D) z y) i₃)) :
    NearBetween (E lam).alphabet.carrier
      (cosetPoints (D.fam lam) (vertex x (geodWord (properRelGenSet D) x y) t)
        (sidePoints (properRelGenSet D) (transEx D E) x y z))
      (12 * δ + (2 * δ + Tb)) ⟨_, h0⟩ ⟨_, h1⟩ := by
  have hw₁ := geodWord_spec (properRelGenSet D) x y
  have hw₂ := geodWord_spec (properRelGenSet D) x z
  have hw₃ := geodWord_spec (properRelGenSet D) z y
  have hprod : ∀ r : RelLetter G Λ, (properRelGenSet D).IsLetter r →
      (transEx D E r).prod = r.val := fun r _ => transEx_prod D E r
  have hb₂ : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x z) i₂ ∈ D.fam lam := QuotientGroup.eq.mp hcos₂
  have hc₂' : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x z) k₂ ∈ D.fam lam :=
    QuotientGroup.eq.mp (hcos₂.trans (mk_vertex_eq_of_isComp (properRelGenSet D) x hw₂.1 hc₂))
  have hb₃ : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex z (geodWord (properRelGenSet D) z y) i₃ ∈ D.fam lam := QuotientGroup.eq.mp hcos₃
  have hc₃' : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex z (geodWord (properRelGenSet D) z y) k₃ ∈ D.fam lam :=
    QuotientGroup.eq.mp (hcos₃.trans (mk_vertex_eq_of_isComp (properRelGenSet D) z hw₃.1 hc₃))
  refine nearBetween_hexagon (E lam).alphabet.symmetricGenerating hδ (X₂ := ⟨_, hc₃'⟩)
    (X₃ := ⟨_, hb₃⟩) (X₄ := ⟨_, hc₂'⟩) (X₅ := ⟨_, hb₂⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact wordDist_cosetCoord_le D E (hTb lam) _ h1 hc₃'
      (exitConnector_mem_relBall (properRelGenSet D) lam (properRelGenSet_base_inv D) hbnd hDc
        hw₁ hw₃ hc₁ hc₃ hcos₃)
  · exact mem_cosetPoints_of_mem _ hc₃'
      (vertex_mem_sidePoints_right (properRelGenSet D) (transEx D E) hprod x y z k₃)
  · exact cosetPoints_side D E (Q := sidePoints (properRelGenSet D) (transEx D E) x y z) z y
      (fun n hn => Or.inr ⟨n, hn, rfl⟩) hc₃ _ hb₃ hc₃'
  · rw [wordDist_comm (E lam).alphabet.symmetricGenerating]
    exact wordDist_cosetCoord_le D E (hTb lam) _ hc₂' hb₃
      (exitEntranceConnector_mem_relBall (properRelGenSet D) lam (properRelGenSet_base_inv D)
        hbnd hDc hw₂ hw₃ hc₂ hc₃ (hcos₂.symm.trans hcos₃))
  · exact mem_cosetPoints_of_mem _ hc₂'
      (vertex_mem_sidePoints_left (properRelGenSet D) (transEx D E) hprod x y z k₂)
  · exact cosetPoints_side D E (Q := sidePoints (properRelGenSet D) (transEx D E) x y z) x z
      (fun n hn => Or.inl ⟨n, hn, rfl⟩) hc₂ _ hb₂ hc₂'
  · exact wordDist_cosetCoord_le D E (hTb lam) _ h0 hb₂
      (entranceConnector_mem_relBall_of_bound (properRelGenSet D) lam
        (properRelGenSet_base_inv D) hbnd hDc hw₁ hw₂ hc₁ hc₂ hcos₂)
  · exact mem_cosetPoints_of_mem _ hb₂
      (vertex_mem_sidePoints_left (properRelGenSet D) (transEx D E) hprod x y z i₂)

/-- **Connected letters are near the other sides** for `properRelGenSet D` and `transEx D E`,
when the members' graphs are `δ`-hyperbolic and `Tb` bounds the expansions of the relative balls
of radius `Dc`. -/
theorem letterNear_properRelGenSet (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {C Dc Tb δ : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon (properRelGenSet D) 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated (properRelGenSet D).fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ (properRelGenSet D).relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hTb : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam Dc → (pieceWord D E lam e).length ≤ Tb)
    (hδ : ∀ lam : Λ, Hyperbolic.IsFourPointHyperbolic (E lam).alphabet.carrier δ) :
    LetterNear (properRelGenSet D) (transEx D E) (transitiveRelGenSet D E).alphabet.carrier
      (12 * δ + (2 * δ + Tb)) := by
  classical
  intro x y z t ht lam e hletter hconn s hs
  have hw₁ := geodWord_spec (properRelGenSet D) x y
  have hel : e ∈ D.fam lam := by
    have h := hw₁.1 _ (List.getElem_mem ht)
    rw [hletter] at h
    exact h
  have hc₁ : IsComp lam (geodWord (properRelGenSet D) x y) t (t + 1) :=
    isComp_succ_of_isCompOf_geodesic (properRelGenSet D) hw₁ ht (by rw [hletter]; exact rfl)
  have hv₁ : vertex x (geodWord (properRelGenSet D) x y) (t + 1)
      = vertex x (geodWord (properRelGenSet D) x y) t * e := by
    have h := vertex_succ (geodWord (properRelGenSet D) x y) x t ht
    rw [hletter] at h
    exact h
  have h0 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) t ∈ D.fam lam := by
    rw [inv_mul_cancel]
    exact one_mem _
  have h1 : (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
      * vertex x (geodWord (properRelGenSet D) x y) (t + 1) ∈ D.fam lam := by
    rw [hv₁, inv_mul_cancel_left]
    exact hel
  have hnb : NearBetween (E lam).alphabet.carrier
      (cosetPoints (D.fam lam) (vertex x (geodWord (properRelGenSet D) x y) t)
        (sidePoints (properRelGenSet D) (transEx D E) x y z))
      (12 * δ + (2 * δ + Tb)) ⟨_, h0⟩ ⟨_, h1⟩ := by
    by_cases h₂ : ∃ i₂ k₂ : ℕ, IsComp lam (geodWord (properRelGenSet D) x z) i₂ k₂ ∧
        (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t) :
            G ⧸ (properRelGenSet D).fam lam)
          = QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x z) i₂)
    · obtain ⟨i₂, k₂, hc₂, hcos₂⟩ := h₂
      by_cases h₃ : ∃ i₃ k₃ : ℕ, IsComp lam (geodWord (properRelGenSet D) z y) i₃ k₃ ∧
          (QuotientGroup.mk (vertex x (geodWord (properRelGenSet D) x y) t) :
              G ⧸ (properRelGenSet D).fam lam)
            = QuotientGroup.mk (vertex z (geodWord (properRelGenSet D) z y) i₃)
      · obtain ⟨i₃, k₃, hc₃, hcos₃⟩ := h₃
        exact nearBetween_hexagon_both D E hbnd hDc hTb (hδ lam) x y z hc₁ h0 h1 hc₂ hcos₂ hc₃
          hcos₃
      · exact (nearBetween_quad_left D E hbnd hDc hTb (hδ lam) x y z hc₁ h0 h1 hc₂ hcos₂
          (fun i k hc hcos => h₃ ⟨i, k, hc, hcos.symm⟩)).mono (by omega)
    · rcases hconn with ⟨i₂, k₂, hc₂, hcos₂⟩ | ⟨i₃, k₃, hc₃, hcos₃⟩
      · exact (h₂ ⟨i₂, k₂, hc₂, hcos₂.symm⟩).elim
      · exact (nearBetween_quad_right D E hbnd hDc hTb (hδ lam) x y z hc₁ h0 h1 hc₃ hcos₃.symm
          (fun i k hc hcos => h₂ ⟨i, k, hc, hcos.symm⟩)).mono (by omega)
  have e1 : (⟨_, h1⟩ : D.fam lam) = ⟨e, hel⟩ :=
    Subtype.ext (show (vertex x (geodWord (properRelGenSet D) x y) t)⁻¹
        * vertex x (geodWord (properRelGenSet D) x y) (t + 1) = e by
      rw [hv₁, inv_mul_cancel_left])
  rw [cosetCoord_self (D.fam lam) _ h0, e1] at hnb
  have hpt := guessPath_in_letter (properRelGenSet D) (transEx D E)
    (fun r _ => transEx_prod D E r) x y ht hs
  rw [hletter, transEx_comp] at hs hpt
  rw [hpt]
  exact exists_near_of_nearBetween D E hel _ hnb hs

end Letter

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_quad_left
#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_quad_right
#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_hexagon_both
#audit_axioms GroupApproximation.GGT.HullLemma35.letterNear_properRelGenSet
