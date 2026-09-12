import GroupApproximation.GGT.DGOLemma421Statement

/-!
# Assembly of the corrected Lemma 4.21(b) output

The geometric part of Dahmani--Guirardel--Osin's argument produces ordered
component starts in the two words, the base-edge separators, and one coset
identity at each start.  This file packages exactly those already-ordered
data and proves the final existential output of the corrected start-coset
statement.  The certificate fixes the two words and the index bound, so it is
strictly smaller than the global Lemma 4.21(b) proposition.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Ordered starts, separators, and start-coset identities for one pair of
words in Lemma 4.21(b).  The ambient endpoint and `W` hypotheses are not
repeated: they are used to produce this certificate, while this record only
assembles its conclusion. -/
structure StartCosetMatchCertificate
    (D : RelGenSet G Λ) (vp vq : G)
    (p q : List (RelLetter G Λ)) (K : ℕ) where
  ip : ℕ → ℕ
  kp : ℕ → ℕ
  iq : ℕ → ℕ
  kq : ℕ → ℕ
  lam : ℕ → Λ
  component_p : ∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)
  component_q : ∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)
  separator_p : ∀ t : ℕ, t + 1 < K →
    BaseEdgeOrTrivial p (kp t) (ip (t + 1))
  separator_q : ∀ t : ℕ, t + 1 < K →
    BaseEdgeOrTrivial q (kq t) (iq (t + 1))
  start_coset : ∀ t : ℕ, t < K →
    (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t)

/-- A fixed ordered start-coset certificate gives the existential conclusion
of the corrected DGO Lemma 4.21(b) clause. -/
theorem StartCosetMatchCertificate.to_exists
    {D : RelGenSet G Λ} {vp vq : G}
    {p q : List (RelLetter G Λ)} {K : ℕ}
    (M : StartCosetMatchCertificate D vp vq p q K) :
    ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Λ),
      (∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)) ∧
      (∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial p (kp t) (ip (t + 1))) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial q (kq t) (iq (t + 1))) ∧
      (∀ t : ℕ, t < K →
        (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t)) := by
  exact ⟨M.ip, M.kp, M.iq, M.kq, M.lam, M.component_p,
    M.component_q, M.separator_p, M.separator_q, M.start_coset⟩

/-- For one requested component, the certificate fields are exactly the
single-index start-coset match used by the source proof. -/
theorem StartCosetMatchCertificate.one_index
    {D : RelGenSet G Λ} {vp vq : G}
    {p q : List (RelLetter G Λ)}
    (M : StartCosetMatchCertificate D vp vq p q 1) :
    ∃ (iP kP iQ kQ : ℕ) (lam : Λ),
      IsComp lam p iP kP ∧ IsComp lam q iQ kQ ∧
      (vertex vp p iP)⁻¹ * vertex vq q iQ ∈ D.fam lam := by
  refine ⟨M.ip 0, M.kp 0, M.iq 0, M.kq 0, M.lam 0, ?_⟩
  exact ⟨M.component_p 0 (by omega), M.component_q 0 (by omega),
    M.start_coset 0 (by omega)⟩

end OsinComponents
end GGT
end GroupApproximation
