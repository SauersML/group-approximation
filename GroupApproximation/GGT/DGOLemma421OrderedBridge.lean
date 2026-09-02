import GroupApproximation.GGT.DGOLemma421Diagram
import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Ordered blocks for the final step of DGO Lemma 4.21(b)

The counting argument in `DGOLemma421Proof` gives a finite block of matched
source components.  The remaining DGO argument orders the target components
and makes the separators explicit.  This module records that ordered-block
payload and proves its direct conversion to the natural-indexed conclusion of
`DGOLemma421b`.  The payload is local to fixed words and a fixed `K`, so it is
strictly smaller than the full lemma and identifies the missing order argument.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Ordered component data for fixed fellow-travelling words.  The guards
`t < K` and `t + 1 < K` match the natural-indexed conclusion in the statement
of DGO Lemma 4.21(b). -/
structure DGO421OrderedBlockPayload
    (D : RelGenSet G Λ) (vp vq : G)
    (p q : List (RelLetter G Λ)) (K : ℕ) where
  ip : ℕ → ℕ
  kp : ℕ → ℕ
  iq : ℕ → ℕ
  kq : ℕ → ℕ
  lam : ℕ → Λ
  pcomp : ∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)
  qcomp : ∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)
  psep : ∀ t : ℕ, t + 1 < K →
    BaseEdgeOrTrivial p (kp t) (ip (t + 1))
  qsep : ∀ t : ℕ, t + 1 < K →
    BaseEdgeOrTrivial q (kq t) (iq (t + 1))
  cosetMatch : ∀ t : ℕ, t < K →
    (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t)

/-- An ordered block payload is exactly the final witness package required by
the natural-indexed form of Lemma 4.21(b). -/
theorem DGO421OrderedBlockPayload.toStartCosetWitness
    {D : RelGenSet G Λ} {vp vq : G} {p q : List (RelLetter G Λ)} {K : ℕ}
    (W : DGO421OrderedBlockPayload D vp vq p q K) :
    ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Λ),
      (∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)) ∧
      (∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial p (kp t) (ip (t + 1))) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial q (kq t) (iq (t + 1))) ∧
      (∀ t : ℕ, t < K →
        (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t)) := by
  exact ⟨W.ip, W.kp, W.iq, W.kq, W.lam,
    W.pcomp, W.qcomp, W.psep, W.qsep, W.cosetMatch⟩

/-! ## What the certificate already decides

Three of the six clauses of the ordered block are consequences of the
certificate, and are proved here rather than assumed.

* the **target index** and the **start-coset identity** at it: the
  certificate's `matched_spec` asserts both, at the basepoints `1` on `p` and
  `pre⁻¹` on `q` --- its `pre` is the geodesic connector `vq⁻¹ vp`, so those
  are exactly the basepoints at which the two paths fellow-travel;
* the **source separator**: the certificate's block is a run of *consecutive*
  peripheral ranks of `p`, and (W1) puts at most one base letter between
  consecutive peripheral letters.

What is left is the target side: the end of the matched component of `q`, its
maximality, and its separator.
-/

/-- The target index the certificate attaches to the `t`-th component of its
matched block.  Only the existence of such an index is asserted there, so it
is selected once here and every clause below is stated at this choice. -/
noncomputable def DGO421FiniteAbsorptionCertificate.blockTarget
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K) (t : Fin K) : ℕ :=
  Classical.choose
    (cert.matched_spec (cert.blockIndex t) (cert.block_matched t))

/-- The selected target index is an index of `q`. -/
theorem DGO421FiniteAbsorptionCertificate.blockTarget_le
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K) (t : Fin K) :
    cert.blockTarget t ≤ q.length :=
  (Classical.choose_spec
    (cert.matched_spec (cert.blockIndex t) (cert.block_matched t))).1

/-- **The start-coset identity of Lemma 4.21(b) is already in the
certificate**, read from the basepoint `1` on `p` and the basepoint `pre⁻¹` on
`q`. -/
theorem DGO421FiniteAbsorptionCertificate.blockTarget_cosetMatch
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K) (t : Fin K) :
    (vertex (1 : G) p (cert.source (cert.blockIndex t)))⁻¹ *
        vertex cert.pre⁻¹ q (cert.blockTarget t) ∈
      D.fam (cert.label (cert.blockIndex t)) := by
  obtain ⟨hgen, hmem, heq⟩ :=
    (Classical.choose_spec
      (cert.matched_spec (cert.blockIndex t) (cert.block_matched t))).2
  have hbt : Classical.choose
      (cert.matched_spec (cert.blockIndex t) (cert.block_matched t)) =
      cert.blockTarget t := rfl
  rw [hbt] at heq
  have hv : vertex cert.pre⁻¹ q (cert.blockTarget t) =
      cert.pre⁻¹ * vertex (1 : G) q (cert.blockTarget t) := by
    have hs := vertex_smul cert.pre⁻¹ (1 : G) q (cert.blockTarget t)
    rwa [mul_one] at hs
  have hval : (vertex (1 : G) p (cert.source (cert.blockIndex t)))⁻¹ *
      (cert.pre⁻¹ * vertex (1 : G) q (cert.blockTarget t)) = hgen := by
    rw [← heq]
    group
  rw [hv, hval]
  exact hmem

/-- The order data still missing after the finite-absorption certificate has
been constructed.  It supplies the end of the matched target component, its
maximality, and the target separator.  No polygon or counting hypotheses occur
in this local record. -/
structure DGO421FiniteAbsorptionOrderData
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K) where
  qEnd : ℕ → ℕ
  qComponent : ∀ (t : ℕ) (ht : t < K),
    IsComp (cert.label (cert.blockIndex ⟨t, ht⟩)) q
      (cert.blockTarget ⟨t, ht⟩) (qEnd t)
  qSeparator : ∀ (t : ℕ) (ht : t + 1 < K),
    BaseEdgeOrTrivial q (qEnd t) (cert.blockTarget ⟨t + 1, ht⟩)

/-! ## The target side reduces to the minimality step

Dahmani--Guirardel--Osin write the two paths as
`p = r₀p₁r₁…p_mr_m` and `q = s₀q₁s₁…q_ns_n`, the `pᵢ`, `qⱼ` peripheral edges
and the `rᵢ`, `sⱼ` either `X`-edges or trivial paths --- which is exactly
`peripheralOccurrence` together with `BaseEdgeOrTrivial`.  Their minimality
argument runs the polygon `Q''` built from the two connecting edges and the
segments of `p` and `q` between them, and concludes "*Hence `a = 1` and
similarly `b = 1`*": the matched targets are **consecutive** peripheral
occurrences of `q`, carrying the label of their partners.

That single conclusion is `DGO421TargetRankData` below, and it is all the
target side needs: the component clause is then the (W3) singleton lemma and
the separator clause is the same successive-rank lemma that already discharges
the source side. -/

/-- The output of the minimality step of Dahmani--Guirardel--Osin's Lemma
4.21(b) on the target side: the certificate's matched targets are consecutive
peripheral occurrences of `q`, and each carries the label of its partner on
`p`.  No polygon, counting or isolation hypothesis occurs here.

The certificate is built over `q` itself.  An earlier version of the counting
proof closed the four-gon over a letter-by-letter substitute for `q`, which
could carry a peripheral letter where `q` carries a base letter and so put a
target where `q` has no component at all.  Carrying Dahmani--Guirardel--Osin's
convention (§4.3: "*Recall that relative generating sets are always assumed
symmetric, so `X = X⁻¹` in the following lemma*") makes the reversed word
admissible outright, so no substitution happens and this record speaks about
the same word the certificate does. -/
structure DGO421TargetRankData
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K) where
  targetRank : Fin K → Fin (peripheralPositions q).card
  targetRank_pos : ∀ t : Fin K,
    (peripheralOccurrence q (targetRank t)).pos = cert.blockTarget t
  targetRank_label : ∀ t : Fin K,
    (peripheralOccurrence q (targetRank t)).label =
      cert.label (cert.blockIndex t)
  targetRank_succ : ∀ (t : ℕ) (ht : t + 1 < K),
    (targetRank ⟨t + 1, ht⟩).val =
      (targetRank ⟨t, Nat.lt_of_succ_lt ht⟩).val + 1

/-- **The minimality output of DGO §4.3 in the form the argument produces it.**

Dahmani--Guirardel--Osin do not exhibit the successor relation directly.  They
choose the matched target of least index and then rule out anything strictly
between: "*if `a > 1`, then there is a component `p_{i+a'}` of `p`,
`0 < a' < a`, which is not isolated in `Q''` ... Hence it is connected to
`q_{j+b'}` for some `b' > 0`.  However this contradicts minimality of `a`.
Hence `a = 1` and similarly `b = 1`*".

So what the polygon argument delivers is the strictness and the emptiness of
the open interval of ranks, and the successor relation is the finite-order
consequence.  This theorem is that last step, so a construction may aim at the
no-intermediate form and never mention successors. -/
noncomputable def DGO421TargetRankData.ofNoIntermediate
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    {cert : DGO421FiniteAbsorptionCertificate D p q N M K}
    (rank : Fin K → Fin (peripheralPositions q).card)
    (hpos : ∀ t : Fin K,
      (peripheralOccurrence q (rank t)).pos = cert.blockTarget t)
    (hlabel : ∀ t : Fin K,
      (peripheralOccurrence q (rank t)).label = cert.label (cert.blockIndex t))
    (hstrict : ∀ (t : ℕ) (ht : t + 1 < K),
      (rank ⟨t, Nat.lt_of_succ_lt ht⟩).val < (rank ⟨t + 1, ht⟩).val)
    (hno : ∀ (t : ℕ) (ht : t + 1 < K),
      ∀ z : Fin (peripheralPositions q).card,
        (rank ⟨t, Nat.lt_of_succ_lt ht⟩).val < z.val →
          z.val < (rank ⟨t + 1, ht⟩).val → False)
    (hK : 0 < K) :
    DGO421TargetRankData cert := by
  let first : Fin K := ⟨0, hK⟩
  let idx : ℕ → Fin K := fun s => if h : s < K then ⟨s, h⟩ else first
  let occ : ℕ → Fin (peripheralPositions q).card := fun s => rank (idx s)
  have hidx : ∀ (s : ℕ) (hs : s < K), idx s = (⟨s, hs⟩ : Fin K) :=
    fun s hs => dif_pos hs
  have hstrict' : ∀ s : ℕ, s + 1 < K → (occ s).val < (occ (s + 1)).val := by
    intro s hs
    have hs0 : s < K := by omega
    simp only [occ, hidx s hs0, hidx (s + 1) hs]
    exact hstrict s hs
  have hno' : ∀ s : ℕ, s + 1 < K →
      ∀ z : Fin (peripheralPositions q).card,
        (occ s).val < z.val → z.val < (occ (s + 1)).val → False := by
    intro s hs z hz1 hz2
    have hs0 : s < K := by omega
    simp only [occ, hidx s hs0, hidx (s + 1) hs] at hz1 hz2
    exact hno s hs z hz1 hz2
  have hsucc := rankSuccessor_of_noIntermediate (K := K) occ hstrict' hno'
  refine
    { targetRank := rank
      targetRank_pos := hpos
      targetRank_label := hlabel
      targetRank_succ := ?_ }
  intro t ht
  have ht0 : t < K := by omega
  have h := hsucc t ht
  simp only [occ, hidx t ht0, hidx (t + 1) ht] at h
  exact h

/-- **Both remaining clauses of the ordered block follow from the minimality
step.**  The component clause is the (W3) singleton lemma at the target rank;
the separator clause is `oppositeContiguity_of_rankSuccessor` on `q`, the same
lemma that discharges the source side from the certificate's own ranks. -/
noncomputable def DGO421TargetRankData.toOrderData
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    {cert : DGO421FiniteAbsorptionCertificate D p q N M K}
    (hW1 : WWord.IsWOne q) (hW3 : WWord.IsWThree D q)
    (T : DGO421TargetRankData cert) (hK : 0 < K) :
    DGO421FiniteAbsorptionOrderData cert := by
  let first : Fin K := ⟨0, hK⟩
  let idx : ℕ → Fin K := fun s => if h : s < K then ⟨s, h⟩ else first
  let iqAt : ℕ → ℕ := fun s => cert.blockTarget (idx s)
  let kqAt : ℕ → ℕ := fun s => cert.blockTarget (idx s) + 1
  let lamAt : ℕ → Λ := fun s => cert.label (cert.blockIndex (idx s))
  have hcomp : ∀ s : ℕ, s < K → IsComp (lamAt s) q (iqAt s) (kqAt s) := by
    intro s _hs
    have hc := PeripheralOccurrence.isComp hW3 (T.targetRank (idx s))
    rw [T.targetRank_label (idx s), T.targetRank_pos (idx s)] at hc
    exact hc
  have hrank : ∀ s : ℕ, s + 1 < K →
      (T.targetRank (idx (s + 1))).val = (T.targetRank (idx s)).val + 1 := by
    intro s hs
    have hs0 : s < K := by omega
    have h1 : idx s = (⟨s, hs0⟩ : Fin K) := dif_pos hs0
    have h2 : idx (s + 1) = (⟨s + 1, hs⟩ : Fin K) := dif_pos hs
    rw [h1, h2]
    exact T.targetRank_succ s hs
  have hsep := oppositeContiguity_of_rankSuccessor hW1 hW3
    (iq := iqAt) (kq := kqAt) (lam := lamAt) hcomp
    (fun s => T.targetRank (idx s))
    (fun s _hs => T.targetRank_pos (idx s))
    hrank
  refine
    { qEnd := kqAt
      qComponent := ?_
      qSeparator := ?_ }
  · intro t ht
    simpa [kqAt, iqAt, lamAt, idx, ht] using hcomp t ht
  · intro t ht
    have ht0 : t < K := by omega
    simpa [kqAt, iqAt, idx, ht0, ht] using hsep t ht

/-- The finite certificate and its order data assemble into the ordered-block
payload.  This is the precise local reduction of the DGO minimality argument:
only `DGO421FiniteAbsorptionOrderData` remains to be constructed. -/
noncomputable def DGO421FiniteAbsorptionOrderData.toPayload
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    {cert : DGO421FiniteAbsorptionCertificate D p q N M K}
    (hW1 : WWord.IsWOne p) (hW3 : WWord.IsWThree D p)
    (O : DGO421FiniteAbsorptionOrderData cert) (hK : 0 < K) :
    DGO421OrderedBlockPayload D (1 : G) cert.pre⁻¹ p q K := by
  let first : Fin K := ⟨0, hK⟩
  let idx : ℕ → Fin K := fun t => if ht : t < K then ⟨t, ht⟩ else first
  let blockAt : ℕ → Fin N := fun t => cert.blockIndex (idx t)
  let ipAt : ℕ → ℕ := fun t => cert.source (blockAt t)
  let kpAt : ℕ → ℕ := fun t => cert.source (blockAt t) + 1
  let lamAt : ℕ → Λ := fun t => cert.label (blockAt t)
  let iqAt : ℕ → ℕ := fun t => cert.blockTarget (idx t)
  let kqAt : ℕ → ℕ := fun t => if _ : t < K then O.qEnd t else O.qEnd 0
  have hrank : ∀ s : ℕ, s + 1 < K →
      (cert.rank (blockAt (s + 1))).val = (cert.rank (blockAt s)).val + 1 := by
    intro s hs
    have hs0 : s < K := by omega
    have hidx0 : idx s = (⟨s, hs0⟩ : Fin K) := dif_pos hs0
    have hidx1 : idx (s + 1) = (⟨s + 1, hs⟩ : Fin K) := dif_pos hs
    have h1 : (blockAt s).val = cert.block.val * K + s := by
      have hform := cert.blockIndex_formula (⟨s, hs0⟩ : Fin K)
      simpa [blockAt, hidx0] using hform
    have h2 : (blockAt (s + 1)).val = cert.block.val * K + (s + 1) := by
      have hform := cert.blockIndex_formula (⟨s + 1, hs⟩ : Fin K)
      simpa [blockAt, hidx1] using hform
    have hlt : (blockAt s).val + 1 < N := by
      have hbound := (blockAt (s + 1)).isLt
      omega
    have heq : blockAt (s + 1) = ⟨(blockAt s).val + 1, hlt⟩ := by
      apply Fin.ext
      show (blockAt (s + 1)).val = (blockAt s).val + 1
      omega
    rw [heq]
    exact cert.rank_succ (blockAt s) hlt
  refine
    { ip := ipAt
      kp := kpAt
      iq := iqAt
      kq := kqAt
      lam := lamAt
      pcomp := ?_
      qcomp := ?_
      psep := ?_
      qsep := ?_
      cosetMatch := ?_ }
  · intro t _ht
    exact cert.source_comp (blockAt t)
  · intro t ht
    simpa [lamAt, iqAt, kqAt, blockAt, idx, ht] using O.qComponent t ht
  · intro t ht
    exact oppositeContiguity_of_rankSuccessor hW1 hW3
      (iq := ipAt) (kq := kpAt) (lam := lamAt)
      (fun s _hs => cert.source_comp (blockAt s))
      (fun s => cert.rank (blockAt s))
      (fun s _hs => cert.rank_pos (blockAt s))
      hrank t ht
  · intro t ht
    have ht0 : t < K := by omega
    simpa [kqAt, iqAt, idx, ht0, ht] using O.qSeparator t ht
  · intro t _ht
    exact cert.blockTarget_cosetMatch (idx t)

/-- **Left translation of an ordered block payload.**  None of the component
or separator clauses mentions a basepoint, and the start-coset clause is
invariant under translating both basepoints, so a payload read from `1` and
`vp⁻¹ vq` is a payload read from `vp` and `vq`. -/
def DGO421OrderedBlockPayload.ofBasepointOne
    {D : RelGenSet G Λ} {vp vq g : G} {p q : List (RelLetter G Λ)} {K : ℕ}
    (hg : g = vp⁻¹ * vq)
    (W : DGO421OrderedBlockPayload D (1 : G) g p q K) :
    DGO421OrderedBlockPayload D vp vq p q K := by
  subst hg
  refine
    { ip := W.ip
      kp := W.kp
      iq := W.iq
      kq := W.kq
      lam := W.lam
      pcomp := W.pcomp
      qcomp := W.qcomp
      psep := W.psep
      qsep := W.qsep
      cosetMatch := ?_ }
  intro t ht
  have hp : vertex vp p (W.ip t) = vp * vertex (1 : G) p (W.ip t) := by
    have hs := vertex_smul vp (1 : G) p (W.ip t)
    rwa [mul_one] at hs
  have hq : vertex vq q (W.iq t) = vp * vertex (vp⁻¹ * vq) q (W.iq t) := by
    have hs := vertex_smul vp (vp⁻¹ * vq) q (W.iq t)
    rwa [mul_inv_cancel_left] at hs
  have hmatch := W.cosetMatch t ht
  rw [hp, hq]
  have hrw : (vp * vertex (1 : G) p (W.ip t))⁻¹ *
      (vp * vertex (vp⁻¹ * vq) q (W.iq t)) =
      (vertex (1 : G) p (W.ip t))⁻¹ * vertex (vp⁻¹ * vq) q (W.iq t) := by
    group
  rw [hrw]
  exact hmatch

/-- **The local reduction of DGO Lemma 4.21(b) at fixed data.**  A
finite-absorption certificate whose connector is the one between the two
basepoints, together with the target-side order data, is the ordered block the
lemma asserts.  Everything except `DGO421FiniteAbsorptionOrderData` is now
supplied by the counting argument. -/
noncomputable def orderedBlockPayload_of_certificate
    {D : RelGenSet G Λ} {vp vq : G} {p q : List (RelLetter G Λ)}
    {N M K : ℕ} (hW1 : WWord.IsWOne p) (hW3 : WWord.IsWThree D p)
    {cert : DGO421FiniteAbsorptionCertificate D p q N M K}
    (hpre : cert.pre = vq⁻¹ * vp)
    (O : DGO421FiniteAbsorptionOrderData cert) (hK : 0 < K) :
    DGO421OrderedBlockPayload D vp vq p q K :=
  DGO421OrderedBlockPayload.ofBasepointOne
    (vp := vp) (vq := vq)
    (by rw [hpre]; group)
    (O.toPayload hW1 hW3 hK)

/-- **Everything in DGO Lemma 4.21(b) except the minimality step.**  From the
counting certificate, its connector identity, and the target ranks, the ordered
block of clause (b) follows outright.  `DGO421TargetRankData` is the whole of
what the geometry still owes. -/
noncomputable def orderedBlockPayload_of_certificate_of_targetRank
    {D : RelGenSet G Λ} {vp vq : G} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    (hW1P : WWord.IsWOne p) (hW3P : WWord.IsWThree D p)
    (hW1Q : WWord.IsWOne q) (hW3Q : WWord.IsWThree D q)
    {cert : DGO421FiniteAbsorptionCertificate D p q N M K}
    (hpre : cert.pre = vq⁻¹ * vp)
    (T : DGO421TargetRankData cert) (hK : 0 < K) :
    DGO421OrderedBlockPayload D vp vq p q K :=
  orderedBlockPayload_of_certificate hW1P hW3P hpre
    (T.toOrderData hW1Q hW3Q hK) hK

/-! ## The ordered-block form of the lemma -/

/-- **DGO Lemma 4.21(b) with the ordered block as its output.**  Its
hypotheses are those of `DGO421FiniteAbsorptionConclusion`; only the
conclusion is strengthened, from the counting certificate to the ordered block
of components.  `dgoLemma421b_of_orderedBlockConclusion` shows it is the whole
of clause (b). -/
def DGO421OrderedBlockConclusion : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    (∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet)) →
      DGO421BaseSymmetric D →
      ∃ C : ℕ, ∀ (eps : ℝ) (K : ℕ),
      0 < eps → 0 < K → ∃ R : ℕ, 0 < R ∧
      ∀ (vp vq : G) (p q : List (RelLetter G Λ)),
        (∀ c ∈ p, D.IsLetter c) → (∀ c ∈ q, D.IsLetter c) →
        WWord.IsWOne p → WWord.IsWTwo D C p → WWord.IsWThree D p →
        WWord.IsWOne q → WWord.IsWTwo D C q → WWord.IsWThree D q →
        R ≤ p.length →
        (wordDist D.alphabet.carrier vp vq : ℝ) ≤ eps →
        (wordDist D.alphabet.carrier (vertex vp p p.length)
          (vertex vq q q.length) : ℝ) ≤ eps →
        Nonempty (DGO421OrderedBlockPayload D vp vq p q K)

/-- The ordered-block conclusion is clause (b): the payload is exactly the
witness tuple the printed statement asserts. -/
theorem dgoLemma421b_of_orderedBlockConclusion
    (h : DGO421OrderedBlockConclusion.{u, w}) : DGOLemma421b.{u, w} := by
  intro G _ Λ D hhyp hbase
  obtain ⟨C, hC⟩ := h G Λ D hhyp hbase
  refine ⟨C, ?_⟩
  intro eps K heps hK
  obtain ⟨R, hR, hRall⟩ := hC eps K heps hK
  refine ⟨R, hR, ?_⟩
  intro vp vq p q hletP hletQ hW1P hW2P hW3P hW1Q hW2Q hW3Q hRlen hstart hend
  obtain ⟨W⟩ := hRall vp vq p q hletP hletQ hW1P hW2P hW3P hW1Q hW2Q hW3Q
    hRlen hstart hend
  exact W.toStartCosetWitness

/-! ## Trivial-group model -/

private def orderedBridgeTrivialRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

private def orderedBridgeTrivialWord : List (RelLetter PUnit Unit) :=
  [RelLetter.comp () 1]

/-- The one-component trivial-group model supplies an ordered payload at
`K = 1`; both separator clauses are vacuous and the start-coset match is the
identity element of the top peripheral subgroup. -/
theorem DGO421OrderedBlockPayload.trivialModel :
    Nonempty (DGO421OrderedBlockPayload orderedBridgeTrivialRelGenSet
      (1 : PUnit) (1 : PUnit)
      orderedBridgeTrivialWord orderedBridgeTrivialWord 1) := by
  let hcomp : IsComp () orderedBridgeTrivialWord 0 1 := by
    refine ⟨by omega, by simp [orderedBridgeTrivialWord], ?_, ?_, ?_⟩
    · intro t ht0 ht1 ht
      have ht' : t = 0 := by omega
      subst ht'
      rfl
    · intro t ht
      omega
    · intro ht
      simp [orderedBridgeTrivialWord] at ht
  let W : DGO421OrderedBlockPayload orderedBridgeTrivialRelGenSet
      (1 : PUnit) (1 : PUnit)
      orderedBridgeTrivialWord orderedBridgeTrivialWord 1 :=
    { ip := fun _ => 0
      kp := fun _ => 1
      iq := fun _ => 0
      kq := fun _ => 1
      lam := fun _ => ()
      pcomp := by
        intro t ht
        simpa [orderedBridgeTrivialWord] using hcomp
      qcomp := by
        intro t ht
        simpa [orderedBridgeTrivialWord] using hcomp
      psep := by
        intro t ht
        omega
      qsep := by
        intro t ht
        omega
      cosetMatch := by
        intro t ht
        simp [orderedBridgeTrivialRelGenSet, orderedBridgeTrivialWord] }
  exact ⟨W⟩

end OsinComponents
end GGT
end GroupApproximation
