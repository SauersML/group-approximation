import GroupApproximation.GGT.DGOLemma421OrderedBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Matched targets in DGO Lemma 4.21(b) are distinct

Uniform Proposition 4.14 isolates distinct components of a deep W-word.
Consequently two distinct selected source components cannot match the same
component of the other word. This proves injectivity of the target assignment;
the increasing-order and no-intermediate-component steps remain separate.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Equal target starts would connect two source components, contradicting
the isolation theorem for W-words. -/
theorem DGO421FiniteAbsorptionCertificate.blockStart_injective
    {D : RelGenSet G Lambda} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {p q : List (RelLetter G Lambda)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K)
    (hletP : ∀ letter ∈ p, D.IsLetter letter)
    (hW1P : WWord.IsWOne p) (hW2P : WWord.IsWTwo D (50 * C) p)
    (hW3P : WWord.IsWThree D p)
    (hletQ : ∀ letter ∈ q, D.IsLetter letter) (hW3Q : WWord.IsWThree D q) :
    Function.Injective cert.blockStart := by
  intro i j hij
  have hlabel : cert.label (cert.blockIndex i) = cert.label (cert.blockIndex j) :=
    isCompStart_label_unique_421 (cert.blockStart_isCompStart hW3Q i)
      (by rw [hij]; exact cert.blockStart_isCompStart hW3Q j)
  have hi := cert.blockStart_cosetMatch hletQ hW3Q i
  have hj := cert.blockStart_cosetMatch hletQ hW3Q j
  rw [← hlabel, ← hij] at hj
  have hconn : Connected D.fam (cert.label (cert.blockIndex i)) 1 p
      (cert.source (cert.blockIndex i)) (cert.source (cert.blockIndex j)) := by
    have hm := (D.fam (cert.label (cert.blockIndex i))).mul_mem hi
      ((D.fam (cert.label (cert.blockIndex i))).inv_mem hj)
    change (vertex (1 : G) p (cert.source (cert.blockIndex i)))⁻¹ *
      vertex (1 : G) p (cert.source (cert.blockIndex j)) ∈ _
    convert hm using 1
    group
  have hrank : cert.rank (cert.blockIndex i) = cert.rank (cert.blockIndex j) := by
    by_contra hne
    apply peripheralOccurrence_not_connected_of_uniformBound hC hbound hletP
      hW1P hW2P hW3P (1 : G) hne
    · rw [cert.rank_label, cert.rank_label]
      exact hlabel.symm
    · rw [cert.rank_label, cert.rank_pos, cert.rank_pos]
      exact hconn
  have hsource : cert.source (cert.blockIndex i) = cert.source (cert.blockIndex j) := by
    rw [← cert.rank_pos, ← cert.rank_pos, hrank]
  have hindices := cert.source_injective hsource
  have hvalues := congrArg Fin.val hindices
  rw [cert.blockIndex_formula, cert.blockIndex_formula] at hvalues
  apply Fin.ext
  omega

/-- The ends of the selected singleton target components are distinct too. -/
theorem DGO421FiniteAbsorptionCertificate.blockTarget_injective
    {D : RelGenSet G Lambda} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {p q : List (RelLetter G Lambda)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K)
    (hletP : ∀ letter ∈ p, D.IsLetter letter)
    (hW1P : WWord.IsWOne p) (hW2P : WWord.IsWTwo D (50 * C) p)
    (hW3P : WWord.IsWThree D p)
    (hletQ : ∀ letter ∈ q, D.IsLetter letter) (hW3Q : WWord.IsWThree D q) :
    Function.Injective cert.blockTarget := by
  intro i j hij
  apply cert.blockStart_injective hC hbound hletP hW1P hW2P hW3P hletQ hW3Q
  exact congrArg (fun n : ℕ => n - 1) hij


/-- Uniform Proposition 4.14 supplies counting certificates with distinct
target starts, at one depth threshold independent of epsilon and block size.
The remaining step is to prove that these distinct targets occur in the
required consecutive order. -/
theorem dgoLemma421b_injectiveTargets_of_uniform414
    (h : DGOProposition414Uniform.{u, w})
    (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (hhyper : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet))
    (hbase : DGO421BaseSymmetric D) :
    ∃ C : ℕ, ∀ (eps : ℝ) (K : ℕ), 0 < eps → 0 < K →
      ∃ R : ℕ, 0 < R ∧
        ∀ (vp vq : G) (p q : List (RelLetter G Lambda)),
          (∀ letter ∈ p, D.IsLetter letter) → (∀ letter ∈ q, D.IsLetter letter) →
          WWord.IsWOne p → WWord.IsWTwo D C p → WWord.IsWThree D p →
          WWord.IsWOne q → WWord.IsWTwo D C q → WWord.IsWThree D q →
          R ≤ p.length →
          (wordDist D.alphabet.carrier vp vq : ℝ) ≤ eps →
          (wordDist D.alphabet.carrier (vertex vp p p.length)
            (vertex vq q q.length) : ℝ) ≤ eps →
          ∃ cert : DGO421FiniteAbsorptionCertificate D p q
            (K * (2 * ⌈eps⌉₊ + 1)) (2 * ⌈eps⌉₊) K,
            cert.pre = vq⁻¹ * vp ∧ Function.Injective cert.blockStart := by
  obtain ⟨Ccount, hcount⟩ :=
    dgoLemma421b_finiteAbsorption_of_uniform414 h G Lambda D hhyper hbase
  obtain ⟨Cisolation, hCisolation, hbound⟩ :=
    dgoUniformSumBound_of_uniform414 h D hhyper hbase 1 1 (by norm_num) (by norm_num)
  refine ⟨max Ccount (50 * Cisolation), ?_⟩
  intro eps K heps hK
  obtain ⟨R, hR, hRall⟩ := hcount eps K heps hK
  refine ⟨R, hR, ?_⟩
  intro vp vq p q hletP hletQ hW1P hW2P hW3P hW1Q hW2Q hW3Q hlen hstart hend
  have hW2Pcount : WWord.IsWTwo D Ccount p :=
    fun i lam x hi hmem => hW2P i lam x hi
      (relBall_mono_radius D lam (Nat.le_max_left _ _) hmem)
  have hW2Qcount : WWord.IsWTwo D Ccount q :=
    fun i lam x hi hmem => hW2Q i lam x hi
      (relBall_mono_radius D lam (Nat.le_max_left _ _) hmem)
  have hW2Pisolation : WWord.IsWTwo D (50 * Cisolation) p :=
    fun i lam x hi hmem => hW2P i lam x hi
      (relBall_mono_radius D lam (Nat.le_max_right _ _) hmem)
  obtain ⟨cert, hpre⟩ := hRall vp vq p q hletP hletQ hW1P hW2Pcount hW3P
    hW1Q hW2Qcount hW3Q hlen hstart hend
  exact ⟨cert, hpre, cert.blockStart_injective hCisolation hbound hletP
    hW1P hW2Pisolation hW3P hletQ hW3Q⟩

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421FiniteAbsorptionCertificate.blockStart_injective
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421FiniteAbsorptionCertificate.blockTarget_injective

#audit_axioms GroupApproximation.GGT.OsinComponents.dgoLemma421b_injectiveTargets_of_uniform414
