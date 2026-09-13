import GroupApproximation.GGT.HullLemma35Sides
import GroupApproximation.GGT.HullLemma35Corner
import GroupApproximation.GGT.OsinLemma55GuessingGeodesics
import GroupApproximation.Algebra.HyperbolicSlimFourPoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: the guessed paths are thin

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  For a hyperbolically
embedded family `D` whose letters are expanded by `ex` into words over a symmetric generating set
`S`, every point of the guessed path from `x` to `y` is within a fixed distance in `Γ(G, S)` of the
guessed paths from `x` to `z` and from `z` to `y` (`thin`):

* a vertex of the geodesic word is `4δ`-close in `Γ(G, X ⊔ H)` to a point between `x` and `z` or
  between `z` and `y`, hence `6δ`-close to a vertex of the other side, and the corner walk from `x`
  or from `y` puts it near the other side (`vertex_near`);
* a point inside the expansion of a component letter is near the other sides when another side meets
  its coset (`LetterNear`), and otherwise the letter is short and the point is near its vertex.

It adapts `GGT/HullSCUnconeThin.lean`.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.Uncone (isBetween_vertex_of_isGeodesicWord
  isComp_succ_of_isCompOf_geodesic span_mem_relBall_of_noComp)

universe u w

section Thin

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A vertex of the side from `x` to `y` is near the other sides.** -/
theorem vertex_near (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc T δ : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (hbase : ∀ b ∈ D.base, wordNorm S b ≤ 1) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val)
    (hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam Dc → wordDist S A B ≤ T)
    (hnear : LetterNear D ex S T)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (x y z : G) {k : ℕ}
    (hk : k ≤ (geodWord D x y).length) :
    ∃ p ∈ sidePoints D ex x y z,
      wordDist S (vertex x (geodWord D x y) k) p ≤ 2 * T + (3 * T + 1) * (6 * δ) := by
  have hSD := D.alphabet.symmetricGenerating
  have hw₁ := geodWord_spec D x y
  have hw₂ := geodWord_spec D x z
  have hw₃ := geodWord_spec D z y
  rcases Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hSD hδ x y z _
      (isBetween_vertex_of_isGeodesicWord D hw₁ hk) with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
  · -- a point between `x` and `z`: walk from the corner `x`
    have hm : wordDist D.alphabet.carrier x q ≤ (geodWord D x z).length := by
      have h1 : wordDist D.alphabet.carrier x q + wordDist D.alphabet.carrier q z
          = wordDist D.alphabet.carrier x z := hq
      have h2 := hw₂.2.2
      omega
    have hbet := isBetween_vertex_of_isGeodesicWord D hw₂ hm
    have hbig := OsinEnlargement.wordDist_le_of_isBetween_of_wordDist_eq hSD hδ hq hbet
      (wordDist_vertex_eq_index D hw₂ hm).symm
    have hu := geodWord_spec D (vertex x (geodWord D x y) k)
      (vertex x (geodWord D x z) (wordDist D.alphabet.carrier x q))
    have hulen : (geodWord D (vertex x (geodWord D x y) k)
        (vertex x (geodWord D x z) (wordDist D.alphabet.carrier x q))).length ≤ 6 * δ := by
      have htri := wordDist_triangle hSD (vertex x (geodWord D x y) k) q
        (vertex x (geodWord D x z) (wordDist D.alphabet.carrier x q))
      rw [hu.2.2]
      omega
    obtain ⟨p, hp, hd⟩ := corner_near D hsymm hbnd hDc hS hbase hball (sidePoints D ex x y z)
      hw₁ hw₂ hk hm hu (fun i _ => vertex_mem_sidePoints_left D ex hprod x y z i)
      (side_left D hsymm hbnd hDc ex hprod hball hnear x y z k)
    refine ⟨p, hp, le_trans hd ?_⟩
    have hmul := Nat.mul_le_mul_left (3 * T + 1) hulen
    omega
  · -- a point between `z` and `y`: walk from the corner `y` on the reversed words
    have hrev₁ := isGeodesicWord_revWord D hsymm hw₁
    have hrev₃ := isGeodesicWord_revWord D hsymm hw₃
    have hq' : Hyperbolic.IsBetween D.alphabet.carrier y q z := by
      have h1 : wordDist D.alphabet.carrier z q + wordDist D.alphabet.carrier q y
          = wordDist D.alphabet.carrier z y := hq
      show wordDist D.alphabet.carrier y q + wordDist D.alphabet.carrier q z
        = wordDist D.alphabet.carrier y z
      rw [wordDist_comm hSD y q, wordDist_comm hSD q z, wordDist_comm hSD y z]
      omega
    have hm : wordDist D.alphabet.carrier y q ≤ (revWord (geodWord D z y)).length := by
      have h1 : wordDist D.alphabet.carrier y q + wordDist D.alphabet.carrier q z
          = wordDist D.alphabet.carrier y z := hq'
      have h2 := hrev₃.2.2
      omega
    have hbet := isBetween_vertex_of_isGeodesicWord D hrev₃ hm
    have hbig := OsinEnlargement.wordDist_le_of_isBetween_of_wordDist_eq hSD hδ hq' hbet
      (wordDist_vertex_eq_index D hrev₃ hm).symm
    have hlen₁ : (revWord (geodWord D x y)).length = (geodWord D x y).length := by
      simp [revWord]
    have hk' : (geodWord D x y).length - k ≤ (revWord (geodWord D x y)).length := by omega
    have hp₀ : vertex y (revWord (geodWord D x y)) ((geodWord D x y).length - k)
        = vertex x (geodWord D x y) k := by
      have h := vertex_revWord_of_end (geodWord D x y) x k
      rwa [hw₁.2.1] at h
    have hu := geodWord_spec D
      (vertex y (revWord (geodWord D x y)) ((geodWord D x y).length - k))
      (vertex y (revWord (geodWord D z y)) (wordDist D.alphabet.carrier y q))
    have hulen : (geodWord D
        (vertex y (revWord (geodWord D x y)) ((geodWord D x y).length - k))
        (vertex y (revWord (geodWord D z y)) (wordDist D.alphabet.carrier y q))).length
          ≤ 6 * δ := by
      have htri := wordDist_triangle hSD (vertex x (geodWord D x y) k) q
        (vertex y (revWord (geodWord D z y)) (wordDist D.alphabet.carrier y q))
      rw [hu.2.2, hp₀]
      omega
    obtain ⟨p, hp, hd⟩ := corner_near D hsymm hbnd hDc hS hbase hball (sidePoints D ex x y z)
      hrev₁ hrev₃ hk' hm hu (fun i hi => vertex_revWord_mem_sidePoints_right D ex hprod x y z hi)
      (side_right D hsymm hbnd hDc hS ex hprod hball hnear x y z _)
    refine ⟨p, hp, ?_⟩
    rw [← hp₀]
    have hmul := Nat.mul_le_mul_left (3 * T + 1) hulen
    omega

/-- **The guessed paths are thin**: `hbaseLen` and `hcompLen` bound the expansions of the base
letters and of the component letters with a short span. -/
theorem thin (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc T δ : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (hbase : ∀ b ∈ D.base, wordNorm S b ≤ 1) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val)
    (hmem : ∀ a : RelLetter G Λ, D.IsLetter a → ∀ s ∈ ex a, s ∈ S)
    (hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam Dc → wordDist S A B ≤ T)
    (hnear : LetterNear D ex S T)
    (hbaseLen : ∀ b ∈ D.base, (ex (RelLetter.base b)).length ≤ T)
    (hcompLen : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam Dc →
      (ex (RelLetter.comp lam e)).length ≤ T)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (x y z : G) {i : ℕ}
    (hi : i ≤ guessLen D ex x y) :
    ∃ p ∈ sidePoints D ex x y z,
      wordDist S (guessPath D ex x y i) p ≤ 2 * T + (3 * T + 1) * (6 * δ) + T := by
  classical
  have hw₁ := geodWord_spec D x y
  rcases exists_letter_block ex (geodWord D x y) i hi with
      ⟨k, hk, rfl⟩ | ⟨k, hk, s, _, hsl, rfl⟩
  · -- a vertex of the geodesic word
    obtain ⟨p, hp, hd⟩ := vertex_near D hsymm hbnd hDc hS hbase ex hprod hball hnear hδ x y z hk
    refine ⟨p, hp, ?_⟩
    rw [guessPath_at_letter D ex hprod x y k]
    omega
  · -- a point strictly inside the expansion of a letter
    have hnearVertex : (ex ((geodWord D x y)[k]'hk)).length ≤ T →
        ∃ p ∈ sidePoints D ex x y z,
          wordDist S (guessPath D ex x y ((expWord ex ((geodWord D x y).take k)).length + s)) p
            ≤ 2 * T + (3 * T + 1) * (6 * δ) + T := by
      intro hlen
      obtain ⟨p, hp, hd⟩ := vertex_near D hsymm hbnd hDc hS hbase ex hprod hball hnear hδ x y z
        (le_of_lt hk)
      have hwalk := wordDist_guessPath_le D ex hS hmem x y
        (Nat.le_add_right (expWord ex ((geodWord D x y).take k)).length s) hi
      rw [guessPath_at_letter D ex hprod x y k] at hwalk
      have htri := wordDist_triangle hS
        (guessPath D ex x y ((expWord ex ((geodWord D x y).take k)).length + s))
        (vertex x (geodWord D x y) k) p
      rw [wordDist_comm hS
        (guessPath D ex x y ((expWord ex ((geodWord D x y).take k)).length + s))
        (vertex x (geodWord D x y) k)] at htri
      exact ⟨p, hp, by omega⟩
    have hlet := hw₁.1 _ (List.getElem_mem hk)
    have hcases : ∀ a : RelLetter G Λ,
        (∃ b, a = RelLetter.base b) ∨ ∃ (lam : Λ) (e : G), a = RelLetter.comp lam e := by
      intro a
      cases a with
      | base b => exact Or.inl ⟨b, rfl⟩
      | comp lam e => exact Or.inr ⟨lam, e, rfl⟩
    rcases hcases ((geodWord D x y)[k]'hk) with ⟨b, hb⟩ | ⟨lam, e, he⟩
    · -- a base letter is short
      apply hnearVertex
      rw [hb] at hlet
      rw [hb]
      exact hbaseLen b hlet
    · by_cases hconn : SideConnected D x y z lam k
      · obtain ⟨p, hp, hd⟩ := hnear x y z k hk lam e he hconn s (le_of_lt hsl)
        exact ⟨p, hp, by omega⟩
      · -- an unconnected component letter has a short span, so it is short
        apply hnearVertex
        have hc : IsComp lam (geodWord D x y) k (k + 1) :=
          isComp_succ_of_isCompOf_geodesic D hw₁ hk (by rw [he]; exact rfl)
        have hno₂ : ∀ i' k' : ℕ, IsComp lam (geodWord D x z) i' k' →
            (QuotientGroup.mk (vertex x (geodWord D x z) i') : G ⧸ D.fam lam)
              ≠ QuotientGroup.mk (vertex x (geodWord D x y) k) :=
          fun i' k' hc' hcos => hconn (Or.inl ⟨i', k', hc', hcos⟩)
        have hno₃ : ∀ i' k' : ℕ, IsComp lam (geodWord D z y) i' k' →
            (QuotientGroup.mk (vertex z (geodWord D z y) i') : G ⧸ D.fam lam)
              ≠ QuotientGroup.mk (vertex x (geodWord D x y) k) :=
          fun i' k' hc' hcos => hconn (Or.inr ⟨i', k', hc', hcos⟩)
        have h0 := span_mem_relBall_of_noComp D lam hsymm hbnd hDc hw₁
          (geodWord_spec D x z) (geodWord_spec D z y) hc hno₂ hno₃
        rw [vertex_succ (geodWord D x y) x k hk, he, inv_mul_cancel_left] at h0
        rw [he]
        exact hcompLen lam e h0

end Thin

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.vertex_near
#audit_axioms GroupApproximation.GGT.HullLemma35.thin
