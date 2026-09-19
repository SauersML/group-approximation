# Audit of arXiv:2607.05283v2 against the t = −1 obstruction

Lane `swarm-0917-w16-w16-z-break` (calibration), 2026-09-19.
Root: `zaremsky-3-05-four-strand-burau-faithful`.
Claim: `burau-preprint-v2-parity-push-fails-for-a-brunnian-four-braid`.

## 0. Summary

- **Source.** V. Bharathram, J. S. Birman, T. E. Brendle, arXiv:2607.05283v2, posted
  2026-09-14, 28 pp., comment "Minor corrections and improved exposition". The PDF was
  downloaded from arxiv.org/pdf/2607.05283v2 and its text extracted with pdfminer on
  2026-09-19. v1 was downloaded too, for comparison. Line numbers below refer to that
  extraction; page numbers are the printed ones.
- **Before this lane.** v2 had been seen only through a summarizer (§10.1 of
  `zp-burau-parity-t-minus-one-obstruction-2026-09-16.md`, marked *preliminary*). The
  definitions behind the refutation (referee checklist item 4 there) had been taken from the
  2026-09-13 check, not re-read from the source.
- **Verdict. v2 is still broken at the same place.**
  - The definitions of the disk sequence and the parity condition (§1), Lemma 4.2, and the
    inclusion `f` (§1) are verbatim as the refutation assumes.
  - Theorem 6.9's proof (the Main Theorem for `Brun_4`) needs, for a conjugate `Φ` of each
    nontrivial Brunnian braid, a `Γ ∈ K_5` with `f(Φ)·Γ` and `Γ` both parity-clean and
    unequal intersection numbers with `α` (Proposition 6.7 and Corollary 6.8, quoted in §2).
  - For `Φ_0 = [(σ_1σ_2)^6, [A_14, [A_24, A_34]]]` no such `Γ` exists for any conjugate
    (§3). So Proposition 6.7 is false at every proper-product conjugate of `Φ_0`, or `Φ_0`
    has no such conjugate and the conjugation step of Theorem 6.9 fails.
- **Localization (§4, conditional).** The v2 proof of Proposition 6.7 checks parity only for
  its first loop `Γ`. For `Φ_0` that loop is forced into the equal-count case. The proof then
  replaces `Γ` by a modified loop `Γ′` and never re-checks parity for `Γ′` or `f(Φ)·Γ′`. For
  `Φ_0` at least one of those two parity claims must fail, unless an earlier step fails.
- **Calibration (§5).** The preprint's own worked example (Section 7) agrees exactly with the
  graph's parity lemma `parity-clean ⟺ |𝕄(−1)| = #crossings`, on all three polynomials it
  prints.

## 1. Definitions in v2, verbatim, and the parity lemma from them

Quotations are from the v2 PDF (pdfminer text; `β_*^3` printed as "β3∗").

- **Moody polynomial** (p. 3): "M(α, β) = Σ_{ℓ∈Z} (t^ℓ · α̃, β̃) t^ℓ where (t^ℓ · α̃, β̃)
  denotes the algebraic intersection number of the lift t^ℓ · α̃ with β̃ in the cover D̃_n".
  It is "only well defined up to multiplication by a power of t".
- **Disk sequence** (p. 6, §3): "Let β = (β3∗)Φ, and as above, we label the points of
  intersection of α with β by q1, . . . , qm according to the order in which we encounter them
  as we travel along β. [...] αi ∪ βi bounds a k-punctured disk ∆i. We define the total winding
  number Wi associated to the disk ∆i to be equal to k if βi is oriented clockwise with respect
  to ∆i, or to be equal to −k otherwise."
- **Lemma 3.1** (Bigelow, p. 6): "Wi = ki+1 − ki."
- **Parity condition** (p. 7): "If ∆ is a disk in the sequence for Φ corresponding to the pair of
  points qi, qi+1 ∈ α ∩ β ∈ ∂∆, then we will say that ∆ is sign-changing if ϵi = −ϵi+1 and
  sign-preserving otherwise. [...] We will say that a braid Φ satisfies the parity condition if a
  disk ∆ in its disk sequence is sign-changing if and only if |P(∆)| is odd."
- **Lemma 4.2** (p. 7): "Let ϕ ∈ Bn. If ϕ satisfies the parity condition, then the Moody
  polynomial of ϕ admits no cancellations."
- **Inclusion** (p. 3, Observation 2.1): "Let f : Bn → Bn+1 be the inclusion map corresponding
  to the standard embedding of Dn into Dn+1." Section 6.3 (p. 19) uses "the induced injection
  f : B4 ↪ B5". This is the standard inclusion used in Proposition 9.1 of the 2026-09-16
  artifact, which settles its checklist item 5.

**Parity lemma, read off the preprint's own definitions.** Take the representative of
`(β_*^3)Φ` on which the disk sequence is computed, with crossings `q_1, ..., q_m` and monomials
`ε_i t^{k_i}`.
- By Lemma 3.1, `k_{i+1} − k_i = W_i = ±|P(∆_i)|`. So `|P(∆_i)|` is odd iff `k_{i+1} − k_i` is
  odd.
- So the parity condition says `ε_{i+1} = −ε_i` iff `k_{i+1} − k_i` is odd. That is,
  `ε_{i+1}(−1)^{k_{i+1}} = ε_i(−1)^{k_i}` for every `i`.
- Hence parity holds iff all `ε_i(−1)^{k_i}` are equal, iff `|M(−1)| = m`.

This is the parity lemma (§6 of the 2026-09-16 artifact), now derived from v2's own text. It
settles checklist item 4 there.

**Parity-clean representatives are minimal.** Let `A` be a parity-clean representative with
`m` crossings, and `A_min` a minimal-position representative.
- `M` depends only on the homology class. This is used in v2's proof of Theorem 2.3 (p. 5):
  "MΦ well defined on the homology class".
- Computing `M` on `A_min` gives `|M(−1)| ≤ |A_min ∩ α| = ι`.
- So `m = |M(−1)| ≤ ι ≤ m`, and every parity-clean representative realizes `ι`.
- So in v2's statements, "satisfies the parity condition" together with `ι` loses nothing by
  reading `ι` as the crossing count of the parity-clean representative. The proof of
  Corollary 6.8 uses exactly this identity (`Σ|a_j| = ι`).

## 2. The load-bearing statements of v2 Section 6, verbatim

- **Proposition 6.7** (p. 20): "Let Φ ∈ B4, and suppose that Φ can be written as a proper
  product Φ = Φ′ · Γ1. Then there exists a push-map Γ ∈ K5 such that f (Φ) · Γ is a proper
  product in B5 and such that both f (Φ) · Γ and Γ satisfy the parity condition. Furthermore we
  may choose Γ so that ι(β3∗ · (Φ · Γ), α) ≠ ι(β3∗ · Γ, α)."
- **Corollary 6.8** (p. 23): "If Φ ∈ K4 admits a proper product Φ = Φ′ · Γ1 and satisfies
  ι(α, (β3∗)Φ) > 0, then there exists a push-map Γ ∈ K5 such that Mf(Φ)·Γ ≠ MΓ."
  - Its proof: "By Proposition 6.7, both Γ and Φ · Γ satisfy the parity condition. It then
    follows from Lemma 4.2 that there are no cancellations [...]". It then writes both
    coefficient sums as `ι`, and ends: "By Proposition 6.7 we can assume that
    ι(α, (β3∗)(f (Φ) · Γ)) ≠ ι(α, (β3∗)Γ). The result follows."
- **Theorem 6.9** (p. 24): "The Burau representation ρ4 is faithful on its restriction to
  Brun4."
  - Its proof conjugates: "Thus we may assume that Φ has been conjugated so that it can be
    written as a proper product Φ = Φ′ · Γ1 for some Φ′ ∈ K4."
  - It then concludes: "By Corollary 6.8, there is some push-map Γ ∈ K5 < B5 so that
    Mf (Φ)·Γ ≠ MΓ."
- **Comparison with v1.** Same mechanism, renumbered: v1 Proposition 6.4 / Corollary 6.5 /
  Theorem 6.6 become v2 Proposition 6.7 / Corollary 6.8 / Theorem 6.9.
  - The new Lemmas 6.4–6.6 ("properly simple modulo 4-disks") make the parity claims for the
    first loop `Γ` explicit. They do not touch the final inequality.
  - The remark after Proposition 6.7 (p. 23) says the construction extends to all `n`, but
    without parity for `Γ_1 ⋯ Γ_k`.

## 3. The obstruction applies to v2 verbatim

**Proposition 3.1.** Let `Φ` be any conjugate in `B_4` of any positive power of
`Φ_0 = [(σ_1σ_2)^6, [A_14, [A_24, A_34]]]`, and let `Γ ∈ B_5` be arbitrary. If `f(Φ)·Γ` and `Γ`
both satisfy the parity condition, then
`ι(α, (β_*^3) f(Φ)Γ) = ι(α, (β_*^3) Γ)`.

*Proof.*
1. By `parity-correcting-push-fails-for-a-brunnian-four-braid` (ESTABLISHED; route
   `parity-correcting-push-fails-via-minus-one-kernel`), parity-clean transverse
   representatives of the two arcs cross `α` equally often.
2. By §1 ("parity-clean representatives are minimal"), each of those counts equals the
   corresponding `ι`. ∎

**Consequences for v2.**
- *Proposition 6.7 is false for `Φ_0`.* Its conclusion demands exactly what Proposition 3.1
  forbids, so it is false for every conjugate of `Φ_0` that is a proper product `Φ′·Γ_1`.
  The proposition also allows `Φ ∈ B_4`, and Proposition 3.1 covers all of them.
- *So the proof of Theorem 6.9 fails at `Φ_0`.* Either some conjugate of `Φ_0` is such a proper
  product, and Proposition 6.7 fails there. Or none is, and the conjugation step of Theorem 6.9
  (p. 24–25) fails. Either way the proof does not cover `Φ_0`.
- *Corollary 6.8's conclusion is not refuted.* The Moody witness `M_{f(Φ_0)Γ} ≠ M_Γ` is expected
  to exist (for `Γ = 1`, §10.3 of the 2026-09-16 artifact). It is only the proof of Corollary 6.8
  that cannot run through parity-clean `Γ` for `Φ_0`.
- *Scope.* The same holds for every `Φ ∈ K_4` with `ρ_4(Φ) ≡ I mod (t+1)`, by the same two
  steps with `burau-minus-one-kernel-meets-brunnian-four-braids` replaced by that hypothesis.
  That set is a large normal subgroup of `Brun_4` (§10.2 of the 2026-09-16 artifact).

## 4. Where the v2 proof of Proposition 6.7 breaks (conditional localization)

Fix a proper-product conjugate `Φ = Φ′·Γ_1` of `Φ_0`, if one exists. The proof (pp. 20–23) runs
as follows.

- **(P1) First loop.** It builds `Γ = γ_2 ∘ γ_1`. It asserts that `f(Φ)·Γ` satisfies parity
  (via Lemma 6.4) and that `Γ` satisfies parity (via Lemma 6.6): "By Lemma 6.6, this Γ
  satisfies the parity condition as well."
- **(P2) Forced equality.** It then says: "It remains to show that we can always choose Γ to
  ensure [...] (2)", and treats the case `ι(α,(β_*^3)Γ) = ι(α,(β_*^3)(Φ·Γ))`. If (P1) holds, then
  Proposition 3.1 forces this equality for `Φ_0`. So for `Φ_0` the proof always enters this
  case.
- **(P3) Modification.** It replaces `γ_2` by `γ_2′ = γ′ ∪ γ″ ∪ γ_2` and sets `Γ′ = γ_1 ∪ γ_2′`.
  It asserts two properties: property 1 gives `ι(α,(β)Γ′) = ι(α,(β)Γ)`, and property 2 says
  `ι(α,(β_*^3)Γ′) > ι(α,(β_*^3)Γ)`. Then: "Since the subarc γ′2 satisfies the two properties
  above, we have established the result in this case."
- **(P4) The silent step.** The proof never re-applies Lemma 6.4 or Lemma 6.6 to `Γ′`. It never
  states that `Γ′` is properly simple modulo 4-disks, which Lemma 6.6 requires. Nor does it
  state that `f(Φ)·Γ′` is a proper product whose 4-disks become sign-changing 5-disks, which
  Lemma 6.4 requires.
  - After (P3), the intersection numbers differ.
  - By Proposition 3.1, at least one of `Γ′` and `f(Φ)·Γ′` then fails the parity condition.

**Conclusion.** For every proper-product conjugate of `Φ_0`, at least one of the following is
false:
- (a) Lemma 6.4 or Lemma 6.6 as applied in (P1);
- (b) one of the two `ι` assertions in (P3);
- (c) the unstated parity of `Γ′` or of `f(Φ)·Γ′` in (P4).

(c) is the natural suspect, because it is the only one of the three that the text never
argues. This matches gap G1 of the 2026-09-13 check of v1, which v2 did not repair: the added
Lemmas 6.4–6.6 argue (P1), not (P4).

This section locates the failure only relative to (a) and (b). It does not verify Lemmas 6.4 and
6.6 or the two `ι` claims, which rest on figures (Figures 6.9–6.12).

## 5. Calibration against the preprint's worked example (Section 7)

Section 7 of v2 (pp. 25–26) prints three unsimplified Moody polynomials, in crossing order. It
states which of them satisfy parity:
- `M_Φ`: "any braid Φ inducing the arc β does not satisfy the parity condition";
- `M_{Φ·Γ}`: "β · Γ [...] now satisfies the parity condition";
- `M_Γ`: "satisfies the parity condition as well".

The script is `experiments/burau-v2-audit-2026-09-17/section7_parity_calibration.py`, with its
log beside it. It uses exact integers and has no inputs.

| polynomial | terms `m` | `M(−1)` | parity by lemma | preprint says | simplified form matches print |
|---|---|---|---|---|---|
| `M_Φ` | 8 | 2 | no | no | yes |
| `M_{Φ·Γ}` | 8 | 8 | yes | yes | yes |
| `M_Γ` | 20 | −20 | yes | yes | yes |

The log ends `PREPRINT SECTION 7 CONSISTENT WITH PARITY LEMMA: True`. So the authors' own
bookkeeping agrees with the criterion `parity ⟺ |M(−1)| = m` on which the obstruction rests.

The example sidesteps the obstruction: by the authors' own statement, its arc `β` is not
`(β_*^3)Φ` for any `Φ ∈ K_4`. Nothing forces `M_{Φ·Γ}(−1) = M_Γ(−1)` there, and indeed
`8 ≠ −20`.

## 6. Referee checklist

1. **Source fidelity.** Quotations come from a pdfminer extraction of the v2 PDF. Line breaks and
   sub- and superscripts were normalized by hand (`β3∗` means `β_*^3`), and the formula
   fragments in Proposition 6.7 and Corollary 6.8 were reassembled from split lines. Please
   re-check them against the PDF, especially the inequality in Proposition 6.7 and the
   conjugation sentence of Theorem 6.9.
2. **Minimality remark (§1).** It needs `|M(−1)| ≤ ι`, which uses that `M` computed on any
   transverse representative is the same Laurent polynomial. That is the homology-class
   invariance used in v2 Theorem 2.3 and in Theorem A of the 2026-09-16 artifact.
3. **Proposition 3.1** imports only the established claim
   `parity-correcting-push-fails-for-a-brunnian-four-braid`.
4. **§4 is conditional** and is not used by any node as a proof.
