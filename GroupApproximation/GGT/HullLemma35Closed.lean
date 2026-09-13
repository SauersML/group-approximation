import GroupApproximation.GGT.HullLemma35Letter
import GroupApproximation.GGT.HullLemma35Thin
import GroupApproximation.GGT.HullLemma35LocalFinite
import GroupApproximation.GGT.HullLemma35Printed
import GroupApproximation.GGT.GuessingGeodesicsCriterion
import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.OsinTheorem54SepSixBound
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5, proved

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (arXiv:1308.4345v2, §3, p. 12):

> Suppose `{H_i}_{i=1}^n ↪h G`, and for each `1 ≤ i ≤ n`, `{K^i_j}_{j=1}^{m_i} ↪h H_i`.
> Then `{K^i_j | 1 ≤ i ≤ n, 1 ≤ j ≤ m_i} ↪h G`.

This module proves it (`printedHullLemma35`). The witness is `transitiveRelGenSet D E`:

* `relBall_finite_transitive` — its relative balls are finite;
* `exists_guessingData_transitive` — the guessed paths of `properRelGenSet D` along `transEx D E`
  satisfy Bowditch's criterion in the Cayley graph of the transitive alphabet, with the thin
  triangle clause from `thin` and `letterNear_properRelGenSet`;
* `isHyperbolicallyEmbedded_transitiveRelGenSet` — so that graph is hyperbolic
  (`OsinEnlargement.exists_isFourPointHyperbolic_of_guessingData`).
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

section Closed

variable {G : Type u} [Group G] {Λ : Type v} {M : Λ → Type w}

/-- **The guessed paths along `transEx D E` satisfy Bowditch's criterion** in the Cayley graph of
the transitive alphabet, when `Λ` is finite and `D` and every `E i` are hyperbolically
embedded. -/
theorem exists_guessingData_transitive (D : RelGenSet G Λ)
    (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) [Finite Λ] (hD : D.IsHyperbolicallyEmbedded)
    (hE : ∀ i : Λ, (E i).IsHyperbolicallyEmbedded) :
    ∃ K : ℕ,
      Nonempty (OsinEnlargement.GuessingData (transitiveRelGenSet D E).alphabet.carrier K) := by
  have hS := (transitiveRelGenSet D E).alphabet.symmetricGenerating
  have hsymm := properRelGenSet_base_inv D
  have hprod : ∀ a : RelLetter G Λ, (properRelGenSet D).IsLetter a →
      (transEx D E a).prod = a.val := fun a _ => transEx_prod D E a
  have hmem := transEx_mem D E
  have hsub : (transitiveRelGenSet D E).alphabet.carrier
      ⊆ (properRelGenSet D).alphabet.carrier := by
    rw [properRelGenSet_alphabet_carrier]
    exact transitive_alphabet_subset D E
  obtain ⟨T₁, hT₁⟩ := exists_pieceWord_length_le D E hD.locallyFinite 1
  have hshort := length_transEx_le_of_wordNorm_le_one D E hT₁
  obtain ⟨δ, hδ⟩ := exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded (properRelGenSet D)
    (isHyperbolicallyEmbedded_properRelGenSet D hD)
  obtain ⟨C, -, hbnd⟩ :=
    sixBound_one_of_fourPointHyperbolic (properRelGenSet D) hsymm hδ 0 le_rfl
  obtain ⟨Tb, hTb⟩ := exists_pieceWord_length_le D E hD.locallyFinite (C * 4)
  choose δf hδf using fun i : Λ =>
    exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded (E i) (hE i)
  obtain ⟨δE, hδE⟩ := (Set.finite_range δf).bddAbove
  have hδE' : ∀ i : Λ, Hyperbolic.IsFourPointHyperbolic (E i).alphabet.carrier δE :=
    fun i => Hyperbolic.IsFourPointHyperbolic.mono (hδE (Set.mem_range_self i)) (hδf i)
  have hTb' : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam (C * 4) →
      (pieceWord D E lam e).length ≤ Tb + 1 :=
    fun lam e he => (hTb lam e he).trans (Nat.le_succ _)
  have hnear := letterNear_properRelGenSet D E hbnd le_rfl hTb' hδE'
  generalize hT : 12 * δE + (2 * δE + (Tb + 1)) = T at hnear
  have hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ (properRelGenSet D).relBall lam (C * 4) →
      wordDist (transitiveRelGenSet D E).alphabet.carrier A B ≤ T := by
    intro lam A B hAB
    have h' := properRelGenSet_relBall_subset D lam (C * 4) hAB
    have h1 := wordNorm_le_length_pieceWord D E (RelGenSet.mem_relBall.mp h').1
    have h2 := hTb' lam _ h'
    show wordNorm (transitiveRelGenSet D E).alphabet.carrier (A⁻¹ * B) ≤ T
    omega
  have hbaseLen : ∀ b ∈ (properRelGenSet D).base,
      (transEx D E (RelLetter.base b)).length ≤ T := by
    intro b _
    rw [transEx_base, List.length_singleton]
    omega
  have hcompLen : ∀ (lam : Λ) (e : G), e ∈ (properRelGenSet D).relBall lam (C * 4) →
      (transEx D E (RelLetter.comp lam e)).length ≤ T := by
    intro lam e he
    rw [transEx_comp]
    have h := hTb' lam e (properRelGenSet_relBall_subset D lam (C * 4) he)
    omega
  have hbase : ∀ b ∈ (properRelGenSet D).base,
      wordNorm (transitiveRelGenSet D E).alphabet.carrier b ≤ 1 := fun b hb =>
    wordNorm_le_one_of_mem
      (show b ∈ (transitiveRelGenSet D E).alphabet.carrier from Or.inl (Or.inl hb))
  refine ⟨(T₁ + 1) + (2 * T + (3 * T + 1) * (6 * δ) + T), ⟨{
    len := guessLen (properRelGenSet D) (transEx D E)
    path := guessPath (properRelGenSet D) (transEx D E)
    start := guessPath_zero (properRelGenSet D) (transEx D E)
    finish := guessPath_len (properRelGenSet D) (transEx D E) hprod
    step := fun x y _ hi => wordDist_guessPath_succ (properRelGenSet D) (transEx D E) hmem x y hi
    short := fun x y hxy i hi j hj =>
      (guessPath_short (properRelGenSet D) (transEx D E) hS hsub hmem hshort x y hxy i hi j
        hj).trans (Nat.le_add_right _ _)
    thin := fun x y z i hi => by
      obtain ⟨p, hp, hd⟩ := HullLemma35.thin (properRelGenSet D) hsymm hbnd le_rfl hS hbase
        (transEx D E) hprod hmem hball hnear hbaseLen hcompLen hδ x y z hi
      rcases hp with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨j, Or.inl ⟨hj, hd.trans (Nat.le_add_left _ _)⟩⟩
      · exact ⟨j, Or.inr ⟨hj, hd.trans (Nat.le_add_left _ _)⟩⟩ }⟩⟩

/-- **The transitive relative generating set is hyperbolically embedded**, when `Λ` is finite
and `D` and every `E i` are. -/
theorem isHyperbolicallyEmbedded_transitiveRelGenSet (D : RelGenSet G Λ)
    (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) [Finite Λ] (hD : D.IsHyperbolicallyEmbedded)
    (hE : ∀ i : Λ, (E i).IsHyperbolicallyEmbedded) :
    (transitiveRelGenSet D E).IsHyperbolicallyEmbedded := by
  obtain ⟨K, ⟨GD⟩⟩ := exists_guessingData_transitive D E hD hE
  obtain ⟨δ, hδ⟩ := OsinEnlargement.exists_isFourPointHyperbolic_of_guessingData
    (transitiveRelGenSet D E).alphabet.symmetricGenerating GD
  exact ⟨⟨(δ : ℝ), isHyperbolicSpace_cayley_of_fourPoint (transitiveRelGenSet D E).alphabet hδ⟩,
    relBall_finite_transitive D E hD.locallyFinite fun i => (hE i).locallyFinite⟩

end Closed

end HullLemma35

universe u

/-- **Hull, Lemma 3.5** (arXiv:1308.4345v2, §3, p. 12), proved at printed generality:

> Suppose `{H_i}_{i=1}^n ↪h G`, and for each `1 ≤ i ≤ n`, `{K^i_j}_{j=1}^{m_i} ↪h H_i`.
> Then `{K^i_j | 1 ≤ i ≤ n, 1 ≤ j ≤ m_i} ↪h G`. -/
theorem printedHullLemma35 : PrintedHullLemma35.{u} := by
  intro G _ n H m K hH hK
  obtain ⟨D, rfl, hD⟩ := hH
  unfold IsHypEmbeddedFamily at hK
  choose E hEK hE using hK
  refine ⟨HullLemma35.transitiveRelGenSet D E, ?_,
    HullLemma35.isHyperbolicallyEmbedded_transitiveRelGenSet D E hD hE⟩
  funext p
  rw [HullLemma35.transitiveRelGenSet_fam, hEK]

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.exists_guessingData_transitive
#audit_axioms GroupApproximation.GGT.HullLemma35.isHyperbolicallyEmbedded_transitiveRelGenSet
#audit_closed_axioms GroupApproximation.GGT.printedHullLemma35
