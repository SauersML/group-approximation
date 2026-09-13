import GroupApproximation.GGT.HullLemma35PieceWords
import GroupApproximation.GGT.HullLemma35PieceGeometry
import GroupApproximation.GGT.HullLemma35Sides
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: the sides of a piece polygon

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  When a component letter
of `properRelGenSet D` on the coset `a H_λ` is expanded along `transEx D E`, the polygon of
`GGT/HullLemma35PieceGeometry.lean` lives in `Γ(H_λ, E λ)` in the coordinates `h ↦ a h`.  This
module supplies its pieces:

* `cosetPoints H a Q` — the coordinates of the points of `Q` on the coset `a H`;
* `wordDist_cosetCoord_le` — a connector in a relative ball is a short side;
* `cosetPoints_side` — the expansion of a component on the coset is a side with its vertices
  among the coset points of the guessed path;
* `exists_near_of_nearBetween` — the bound on the polygon moves back to `Γ(G, transitive
  alphabet)`.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.Uncone (exists_comp_of_isCompOf)

universe u v w

section PieceSides

variable {G : Type u} [Group G] {Λ : Type v} {M : Λ → Type w}

/-- **The points of `Q` on the coset `a H`**, in the coordinates `h ↦ a h`. -/
def cosetPoints (H : Subgroup G) (a : G) (Q : Set G) : Set H :=
  {h | a * (h : G) ∈ Q}

theorem mem_cosetPoints_of_mem {H : Subgroup G} {Q : Set G} (a : G) {u : G}
    (hu : a⁻¹ * u ∈ H) (hQ : u ∈ Q) : (⟨_, hu⟩ : H) ∈ cosetPoints H a Q := by
  show a * (a⁻¹ * u) ∈ Q
  rw [mul_inv_cancel_left]
  exact hQ

theorem cosetCoord_self (H : Subgroup G) (a : G) (h : a⁻¹ * a ∈ H) : (⟨_, h⟩ : H) = 1 :=
  Subtype.ext (inv_mul_cancel a)

/-- **A step of `E lam` is a transitive letter**, so the inclusion of `H lam` shortens words. -/
theorem wordNorm_subtype_le_transitive (D : RelGenSet G Λ)
    (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) (lam : Λ) (h : D.fam lam) :
    wordNorm (transitiveRelGenSet D E).alphabet.carrier (h : G)
      ≤ wordNorm (E lam).alphabet.carrier h := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq (E lam).alphabet.symmetricGenerating h
  have hw : IsWord (transitiveRelGenSet D E).alphabet.carrier (l.map (D.fam lam).subtype)
      (h : G) := by
    refine ⟨fun s hs => ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      rcases hl.letters t ht with hb | hf
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨lam, ⟨t, hb, rfl⟩⟩))
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hf
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨lam, j⟩, ⟨t, hj, rfl⟩⟩)
    · show (l.map (D.fam lam).subtype).prod = (D.fam lam).subtype h
      rw [← MonoidHom.map_list_prod, hl.prod_eq]
  have h1 := wordNorm_le_length hw
  rw [List.length_map, hlen] at h1
  exact h1

/-- **Translating the Cayley graph of a member** into `Γ(G, transitive alphabet)`. -/
theorem wordDist_mul_subtype_le (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    (lam : Λ) (a : G) (h h' : D.fam lam) :
    wordDist (transitiveRelGenSet D E).alphabet.carrier (a * (h : G)) (a * (h' : G))
      ≤ wordDist (E lam).alphabet.carrier h h' := by
  rw [wordDist_left_invariant]
  exact wordNorm_subtype_le_transitive D E lam (h⁻¹ * h')

/-- **A connector in a relative ball is a short side** of `Γ(H lam, E lam)`, when `Tb` bounds the
expansions of the ball. -/
theorem wordDist_cosetCoord_le (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {lam : Λ} {Tb n : ℕ}
    (hTb : ∀ e : G, e ∈ D.relBall lam n → (pieceWord D E lam e).length ≤ Tb) (a : G) {u v : G}
    (hu : a⁻¹ * u ∈ D.fam lam) (hv : a⁻¹ * v ∈ D.fam lam)
    (huv : u⁻¹ * v ∈ (properRelGenSet D).relBall lam n) :
    wordDist (E lam).alphabet.carrier ⟨_, hu⟩ ⟨_, hv⟩ ≤ Tb := by
  have hball := properRelGenSet_relBall_subset D lam n huv
  have hm : u⁻¹ * v ∈ D.fam lam := (RelGenSet.mem_relBall.mp hball).1
  have heq : (⟨_, hu⟩ : D.fam lam)⁻¹ * ⟨_, hv⟩ = ⟨u⁻¹ * v, hm⟩ :=
    Subtype.ext (show (a⁻¹ * u)⁻¹ * (a⁻¹ * v) = u⁻¹ * v by group)
  show wordNorm (E lam).alphabet.carrier ((⟨_, hu⟩ : D.fam lam)⁻¹ * ⟨_, hv⟩) ≤ Tb
  rw [heq, ← length_pieceWord_of_mem D E hm]
  exact hTb _ hball

/-- **The expansion of a component on the coset of `a` is a geodesic side** of `Γ(H lam, E lam)`,
with its vertices among the coset points of any set `Q` holding the guessed path from `f` to `g`. -/
theorem cosetPoints_side (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {Q : Set G} (f g : G)
    (hQ : ∀ n ≤ guessLen (properRelGenSet D) (transEx D E) f g,
      guessPath (properRelGenSet D) (transEx D E) f g n ∈ Q)
    {lam : Λ} {i k : ℕ} (hc : IsComp lam (geodWord (properRelGenSet D) f g) i k) (a : G)
    (hb : a⁻¹ * vertex f (geodWord (properRelGenSet D) f g) i ∈ D.fam lam)
    (hb' : a⁻¹ * vertex f (geodWord (properRelGenSet D) f g) k ∈ D.fam lam) :
    ∀ m ≤ wordDist (E lam).alphabet.carrier ⟨_, hb⟩ ⟨_, hb'⟩,
      ∃ c ∈ cosetPoints (D.fam lam) a Q,
        Hyperbolic.IsBetween (E lam).alphabet.carrier ⟨_, hb⟩ c ⟨_, hb'⟩ ∧
          wordDist (E lam).alphabet.carrier ⟨_, hb⟩ c = m := by
  classical
  have hw := geodWord_spec (properRelGenSet D) f g
  obtain rfl : k = i + 1 := isComp_eq_succ_of_isGeodesicWord (properRelGenSet D) lam hw hc
  have hi : i < (geodWord (properRelGenSet D) f g).length := by
    have h2 := hc.2.1
    omega
  obtain ⟨e, he⟩ := exists_comp_of_isCompOf (hc.2.2.1 i le_rfl (by omega) hi)
  have hel : e ∈ D.fam lam := by
    have h := hw.1 _ (List.getElem_mem hi)
    rw [he] at h
    exact h
  have hv : vertex f (geodWord (properRelGenSet D) f g) (i + 1)
      = vertex f (geodWord (properRelGenSet D) f g) i * e := by
    have h := vertex_succ (geodWord (properRelGenSet D) f g) f i hi
    rw [he] at h
    exact h
  have hX : (⟨_, hb'⟩ : D.fam lam) = ⟨_, hb⟩ * ⟨e, hel⟩ := by
    apply Subtype.ext
    show a⁻¹ * vertex f (geodWord (properRelGenSet D) f g) (i + 1)
      = a⁻¹ * vertex f (geodWord (properRelGenSet D) f g) i * e
    rw [hv, mul_assoc]
  have hspec := geodList_spec (E lam).alphabet.symmetricGenerating ⟨e, hel⟩
  have hdist : wordDist (E lam).alphabet.carrier ⟨_, hb⟩ ⟨_, hb'⟩
      = (geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).length := by
    rw [hX, hspec.2]
    unfold wordDist
    rw [inv_mul_cancel_left]
  intro m hm
  rw [hdist] at hm
  obtain ⟨hbet, hd⟩ :=
    isBetween_mul_prod_take (E lam).alphabet.symmetricGenerating hspec.1 hspec.2 ⟨_, hb⟩ hm
  refine ⟨⟨_, hb⟩ * ((geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).take m).prod,
    ?_, ?_, hd⟩
  · have hlen : m ≤ (transEx D E ((geodWord (properRelGenSet D) f g)[i]'hi)).length := by
      rw [he, transEx_comp, length_pieceWord_of_mem D E hel, ← hspec.2]
      exact hm
    have hpt := guessPath_in_letter (properRelGenSet D) (transEx D E)
      (fun r _ => transEx_prod D E r) f g hi hlen
    have hin := hQ
      ((expWord (transEx D E) ((geodWord (properRelGenSet D) f g).take i)).length + m) (by
        have h2 := length_expWord_take_add_le (transEx D E) (geodWord (properRelGenSet D) f g) hi
        unfold guessLen guessWord
        omega)
    rw [hpt, he, transEx_comp, prod_take_pieceWord D E hel] at hin
    have hcoe : a * ((⟨_, hb⟩ * ((geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).take
          m).prod : D.fam lam) : G)
        = vertex f (geodWord (properRelGenSet D) f g) i * (D.fam lam).subtype
          ((geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).take m).prod := by
      show a * (a⁻¹ * vertex f (geodWord (properRelGenSet D) f g) i
          * (((geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).take m).prod : G))
        = vertex f (geodWord (properRelGenSet D) f g) i
          * (((geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).take m).prod : G)
      rw [← mul_assoc, mul_inv_cancel_left]
    show a * ((⟨_, hb⟩ * ((geodList (E lam).alphabet.symmetricGenerating ⟨e, hel⟩).take
      m).prod : D.fam lam) : G) ∈ Q
    rw [hcoe]
    exact hin
  · rw [hX]
    exact hbet

/-- **The bound on the polygon moves back to the transitive alphabet**: if the points between `1`
and `e` in `Γ(H lam, E lam)` are within `K` of the coset points of `Q`, then so is every prefix of
the expansion of `e`, translated by `a`. -/
theorem exists_near_of_nearBetween (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {Q : Set G} {lam : Λ} {e : G} (he : e ∈ D.fam lam) (a : G) {K : ℕ}
    (hnb : NearBetween (E lam).alphabet.carrier (cosetPoints (D.fam lam) a Q) K 1 ⟨e, he⟩)
    {s : ℕ} (hs : s ≤ (pieceWord D E lam e).length) :
    ∃ p ∈ Q, wordDist (transitiveRelGenSet D E).alphabet.carrier
      (a * ((pieceWord D E lam e).take s).prod) p ≤ K := by
  have hspec := geodList_spec (E lam).alphabet.symmetricGenerating ⟨e, he⟩
  rw [length_pieceWord_of_mem D E he, ← hspec.2] at hs
  obtain ⟨hbet, _⟩ :=
    isBetween_mul_prod_take (E lam).alphabet.symmetricGenerating hspec.1 hspec.2 1 hs
  rw [one_mul, one_mul] at hbet
  obtain ⟨p, hp, hd⟩ := hnb _ hbet
  refine ⟨a * (p : G), hp, ?_⟩
  rw [prod_take_pieceWord D E he]
  exact le_trans (wordDist_mul_subtype_le D E lam a
    ((geodList (E lam).alphabet.symmetricGenerating ⟨e, he⟩).take s).prod p) hd

end PieceSides

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.wordDist_mul_subtype_le
#audit_axioms GroupApproximation.GGT.HullLemma35.wordDist_cosetCoord_le
#audit_axioms GroupApproximation.GGT.HullLemma35.cosetPoints_side
#audit_axioms GroupApproximation.GGT.HullLemma35.exists_near_of_nearBetween
