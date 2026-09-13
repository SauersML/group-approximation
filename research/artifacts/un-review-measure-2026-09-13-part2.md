---
rg: 2
title: "UN review, trace side: un-traces Kazhdan collapse, ring criterion and corona (MF) traces (2026-09-13)"
kind: artifact
---

Lane `un-verify-measure`, 2026-09-13. Part 2 of 2 (part 1: `un-review-measure-2026-09-13-part1.md`).
Reviewed: the `un-traces` landing 102def4e00, read at tip b590ad02a4 and rechecked at b9ba6293f1 (unchanged).
Verdict key as in part 1. There is no FAIL.

## T0 `ozawa-kazhdan-liftable-traces-are-fd-limits` (+ `-citation`): PASS

arXiv:math/0306067v2 was fetched on MSI and pages 21, 24 and 26 were extracted with pdftotext locally.
- Theorem 6.1 (i), (ii), (ii'), (iii), (iv) match verbatim. The omitted last sentence, on compressions when
  A ∩ K(H) = {0}, is not used.
- Definition 7.2 matches verbatim.
- Theorem 7.4 and its "In particular" sentence match verbatim.
- The p. 26 remark ("infinite simple groups with Kazhdan's property (T) ... do not have the property (F) as it was shown
  by Kirchberg [Ki3]") matches verbatim.

## T1 `kazhdan-trace-amenable-iff-qd-iff-fd-limit`: PASS on the mathematics; GAP (subsumption and credit)

- **Re-derived.**
  - (c)⇒(b) and (b)⇒(a) (|tr x| ≤ ‖x‖, and φ(b*) = φ(b)* for ucp maps) check.
  - (a)⇒(c): Thm 6.1 (ii)⇒(ii'), then Thm 7.4.
  - For RF ⇒ (c) with π_m = λ_{Γ/N_m}: tr π_m(u_g) = [g ∈ N_m] → δ_{g,e}.
  - (a)⇒RF is the last sentence of Thm 7.4.
- **GAP, subsumption.** The older established node `stw10-kazhdan-full-group-traces-are-qd` (Brown, Mem. AMS 184,
  Prop. 4.1.12, via Kirchberg's rigidity lemma) already proves that every amenable trace on C*(Γ), Γ Kazhdan, is a
  pointwise limit of traces of finite-dimensional representations, hence quasidiagonal. That is (a)⇒(c)⇒(b).
  - The remaining clauses are trivial converses plus Kirchberg's (F)+(T) ⇒ RF.
  - So the node is a restatement, packaged with Ozawa's formulation.
  - Corrected at review: a `distinct_from` entry and a credit line pointing to `stw10-kazhdan-full-group-traces-are-qd`.

## T2 `elementary-group-trace-amenable-iff-ring-residually-finite`: PASS

- **R RF ⇒ G RF.** Check a nonzero entry of g − 1 modulo a finite-index ideal.
- **G RF ⇒ R RF.** Re-derived with the convention [x,y] = xyx^{-1}y^{-1}, so [e_12(a), e_23(b)] = e_13(ab).
  - For a ∈ I, both e_13(ab) and e_13(ba) lie in N, so I = lev(N) is a two-sided ideal.
  - a ↦ e_12(a)N has kernel I (`elementary-root-kernel-equals-level`), so R/I injects into G/N.
- **Corollary A.** A simple infinite ring has no proper finite-index ideal.
- **Corollary B.** Q^{2m} a summand of Q^m forces |Q| ≤ 1.
- **Corollary C.** {rk = 0} is a proper ideal of a simple ring, so the rank function is faithful, while τ is not QD
  by A. The refutation stands.
- **Subsumption.** Scanned the 21 files mentioning factorization, residual finiteness and (T) (full list in the lane
  dir). `binary-leavitt-unit-group-fails-factorization-property` and `rank-twelve-leavitt-group-lacks-factorization-property`
  are special cases of Corollary A or B by different means. There is no conflict.

## T3 `lef-group-canonical-trace-is-a-corona-trace`: PASS on the mathematics; GAP (naming and credit)

- **(a).** Φ(u_g) = 1 forces τ_G(u_g) = tr_ω(1) = 1, so g = e and G embeds in U(Q_d).
- **(b).** Windows B_k and partial embeddings σ_k with σ_k(e) = e, since σ_k(e)² = σ_k(e). Θ_k(g) = λ(σ_k(g)) is exactly
  multiplicative eventually, and tr λ(σ_k(g)) = [σ_k(g) = e] → δ_{g,e}. Both sides are states agreeing on the spanning
  unitaries.
- **GAP, naming (relayed from un-novelty, verified at review).**
  - A corona trace is an MF trace. C. Schafhauser, *MF traces and the Cuntz semigroup*, arXiv:1705.06555, abstract
    read from arXiv on MSI: "A trace τ on a separable C*-algebra A is called matricial field (MF) if there is a
    trace-preserving morphism from A to Q_ω, where Q_ω denotes the norm ultrapower of the universal UHF-algebra Q."
  - For separable C*_max(G) the notions agree. A corona trace composes Q_d → ∏_ω M_{d_k}/c_ω ↪ Q_ω trace-preservingly.
    Conversely, separability extracts a sequence into Q_d with traces converging along a subsequence.
  - The graph's `hyperlinear-trace-not-mf-trace` and `faithful-mf-models-realize-all-mf-traces` use the same notion.
  - Part (b) also overlaps `lef-implies-operator-mf`, with the trace recorded; the node says so.
  - Corrected at review: title and naming paragraph. Ids keep the word `corona`.

## T4 `quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift`: PASS; GAP (naming, as T3)

- A ucp lift (φ_k) is norm-asymptotically multiplicative, with tr∘φ_k → τ_G along ω.
- Separability gives a subsequence with weak* convergence, so τ_G is QD. T1 (equivalently `stw10-kazhdan-full-group-traces-are-qd`
  with Kirchberg) then gives RF.
- **Witnesses.** G = EL_3(LC(X,F_q)⋊Z): a finite-index normal subgroup is central (impossible, since G is infinite and Z
  finite) or all of G. S = G/Z is infinite and simple.

## T5 `corona-traces-separate-paradox-from-measure-for-el-n`: PASS on (ii)–(iv); (i) CONDITIONAL; GAP (scope and naming)

- **(i).** Conditional on un-paradox's unreviewed `stably-infinite-ring-elementary-groups-have-no-mf-quotient`. Its case
  n = 1 is `full-defect-ring-non-mf-at-rank-two`, tex Thm l.918.
  - Manuscript Lemma `prop:mf-residual-calculus`, read verbatim at tip: "Let G be countable and K ≤ G. Every
    homomorphism from G to an MF group is trivial on K if and only if every corona homomorphism from G is trivial on K."
  - Given that, every corona trace is the trivial character.
- **(ii).** A countable subgroup of ∏_ω GL_{N N_k}(F_{q_k}) is LEF, then T3(b) applies. It uses varying finite fields,
  which is consistent with F1.
- **(iii).** The peer root `subshift-elementary-mf-iff-word-edges-lie-on-cycles` (route
  `subshift-rank-four-mf-dichotomy-proof` on main) states MF ⟺ LEF ⟺ R_X directly finite for n ≥ 4. With T3(a),(b)
  the chain closes.
- **(iv).** This is T2 Corollary A.
- **GAP, scope.** Following un-novelty: this is a trace-level reading of tex Thm l.918 (through the stably-infinite
  extension) and of LEF embeddings, stated with MF traces. It is not a new invariant. Corrected at review.

## T6 open nodes: display checked

- `directly-finite-simple-ring-el-n-trace-is-corona-trace` (OPEN). The necessity bullet is correct: tex Cor l.1016
  gives direct finiteness from a nontrivial MF quotient over a simple ring. Naming paragraph added.
- `directly-finite-subshift-el-n-reduced-cstar-is-mf` (OPEN). **GAP, wording.** An embedding of C*_r(G) into a corona
  gives operator MF with reduced norms, i.e. clauses (1) and (3) of GKMP, not the trace clause (2). "GKMP-type MF"
  overstated this. Corrected at review.

## Artifact §6 (reduced side), not a node

The invariant-mean argument from Thm 6.1(i) applied to C*_r(G) ⊆ B(ℓ²G) is correct: φ(λ_g f λ_g*) = φ(f λ_g* λ_g) = φ(f).
Rosenberg and Kesten are recalled, as the artifact says.
