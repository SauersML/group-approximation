import GroupApproximation.GGT.DGOLemma421OrderedBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# The single-match case of DGO Lemma 4.21(b)

The finite-absorption argument already finds a matched component on each
word. For a block of size one the target-order condition is empty, so this
case follows from uniform Proposition 4.14 without the remaining consecutive
target argument. The output retains the actual basepoints and both maximal
components, and uses the existing ordered-block type.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The counting certificate alone gives the complete one-component block.
No target-order producer is required for a singleton block. -/
noncomputable def DGO421FiniteAbsorptionCertificate.singleMatch
    {D : RelGenSet G Lambda} {vp vq : G}
    {p q : List (RelLetter G Lambda)} {N M : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M 1)
    (hpre : cert.pre = vq⁻¹ * vp)
    (hletQ : ∀ letter ∈ q, D.IsLetter letter) (hW3Q : WWord.IsWThree D q) :
    DGO421OrderedBlockPayload D vp vq p q 1 := by
  let index : Fin 1 := 0
  apply DGO421OrderedBlockPayload.ofBasepointOne (g := cert.pre⁻¹)
    (by rw [hpre]; group)
  exact {
    ip := fun _ => cert.source (cert.blockIndex index)
    kp := fun _ => cert.source (cert.blockIndex index) + 1
    iq := fun _ => cert.blockStart index
    kq := fun _ => cert.blockTarget index
    lam := fun _ => cert.label (cert.blockIndex index)
    pcomp := fun _ _ => cert.source_comp (cert.blockIndex index)
    qcomp := fun _ _ => cert.blockStart_isComp hW3Q index
    psep := by intro t ht; omega
    qsep := by intro t ht; omega
    cosetMatch := fun _ _ => cert.blockStart_cosetMatch hletQ hW3Q index }

/-- The `K = 1` case of DGO Lemma 4.21(b), reduced to uniform Proposition
4.14. This is a conditional reduction, not a closed proof of Proposition
4.14 or of the general consecutive-block statement. -/
theorem dgoLemma421b_singleMatch_of_uniform414
    (h : DGOProposition414Uniform.{u, w})
    (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (hhyper : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet))
    (hbase : DGO421BaseSymmetric D) :
    ∃ C : ℕ, ∀ eps : ℝ, 0 < eps → ∃ R : ℕ, 0 < R ∧
      ∀ (vp vq : G) (p q : List (RelLetter G Lambda)),
        (∀ letter ∈ p, D.IsLetter letter) → (∀ letter ∈ q, D.IsLetter letter) →
        WWord.IsWOne p → WWord.IsWTwo D C p → WWord.IsWThree D p →
        WWord.IsWOne q → WWord.IsWTwo D C q → WWord.IsWThree D q →
        R ≤ p.length →
        (wordDist D.alphabet.carrier vp vq : ℝ) ≤ eps →
        (wordDist D.alphabet.carrier (vertex vp p p.length)
          (vertex vq q q.length) : ℝ) ≤ eps →
        Nonempty (DGO421OrderedBlockPayload D vp vq p q 1) := by
  obtain ⟨C, hC⟩ := dgoLemma421b_finiteAbsorption_of_uniform414 h G Lambda D hhyper hbase
  refine ⟨C, ?_⟩
  intro eps heps
  obtain ⟨R, hR, hRall⟩ := hC eps 1 heps (by omega)
  refine ⟨R, hR, ?_⟩
  intro vp vq p q hletP hletQ hW1P hW2P hW3P hW1Q hW2Q hW3Q hlen hstart hend
  obtain ⟨cert, hpre⟩ := hRall vp vq p q hletP hletQ hW1P hW2P hW3P
    hW1Q hW2Q hW3Q hlen hstart hend
  exact ⟨cert.singleMatch hpre hletQ hW3Q⟩

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421FiniteAbsorptionCertificate.singleMatch
#audit_axioms GroupApproximation.GGT.OsinComponents.dgoLemma421b_singleMatch_of_uniform414
