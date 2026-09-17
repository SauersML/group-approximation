---
rg: 2
id: titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair
kind: claim
title: The Titz--Witzel kernel is nonsofic exactly when every almost solution of its relators becomes monodromy-free after deleting o(n) points, and every almost solution has consistency deficit at least a fixed multiple of its mark
distinct_from:
  infinite-simple-group-permutation-stable-iff-nonsofic: that equates nonsoficity of a simple group with the collapse of every almost action; this replaces collapse by the weaker, purely combinatorial deletion repair (removing o(n) points kills all monodromy), and the passage back to collapse is property (T), through the partial-action rounding theorem.
  titz-witzel-soficity-is-one-finite-csp: that equates soficity with a marked finite gate; this equates the negation with a repair property of all gate solutions, with an explicit deficit-versus-mark inequality in between.
  titz-witzel-kernel-nonsofic: that is the open nonsoficity assertion; this is an established equivalent form of it, not a proof.
  kazhdan-consistent-partial-models-round-to-finite-actions: that is the general rounding theorem; this is its application to the kernel, together with the converse, which needs simplicity.
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts). It is not established because
two referee lenses refuted the node as written: the remark on (P2) cites a calibration that does not
show it, and item 3 overstates an imported filling-radius bound. Both lenses found items 1 and 2
sound.

Let `K = <S | R>` be a finite presentation of the smallest Titz
Mite--Witzel kernel of `titz-witzel-kernel-sofic`, with `S` symmetric, and let `kappa` be a
Kazhdan constant for `S` in the convention (KP) of
`kazhdan-consistent-partial-models-round-to-finite-actions`. An *almost solution* is a sequence
`sigma_j : S -> Sym(n_j)` with `d_H(sigma_j(r), 1) -> 0` for every `r in R`. A set `A` is
*consistent* as in `kazhdan-consistent-partial-models-round-to-finite-actions`. The *consistency
deficit* `eta(sigma)` is the least `|[n] \ A|/n` over consistent sets `A`.

1. **Deficit inequality.** For every `sigma : S -> Sym(n)`,

   ```text
   max_(s in S) d_H(sigma(s), 1) <= (2 + 2/kappa^2) eta(sigma).                  (DR1)
   ```

2. **Equivalence.** The following are equivalent.
   * (a) `K` is not sofic.
   * (b) **Deletion repair.** Every almost solution has `eta(sigma_j) -> 0`.
   * (c) Every almost solution has `max_s d_H(sigma_j(s), 1) -> 0`.
   * (d) Every almost solution satisfies `d_H(sigma_j(w), 1) -> 0` for every word `w`.

3. **Soficity form.** `K` is sofic iff some almost solution has `liminf_j eta(sigma_j) > 0`. When
   this holds, the solution may be taken to have `liminf_j max_s d_H(sigma_j(s),1) > 0`. Every
   consistent set of such a solution then misses at least `c_kappa m n_j` points, where
   `c_kappa = kappa^2/(2kappa^2+2)` and `m` is the mark. The open trivial words live at filling
   radius of order `log(1/eps_j)` (`kazhdan-sofic-models-carry-long-scale-monodromy`).

**Why this decomposition.** The nonsoficity direction `titz-witzel-kernel-nonsofic` splits into
two prerequisites, each of which can fail separately.

* **(P1) Rounding.** Consistent sets of density `1 - eta` force collapse at rate `O(eta)`. This is
  item 1, ESTABLISHED, and it is where property (T) and the absence of finite quotients are used
  up.
* **(P2) Deletion repair.** Every almost solution of `K` becomes consistent after deleting `o(n)`
  points. This is item 2(b), OPEN, and equivalent to the target. It concerns only monodromy of
  trivial words inside the Schreier graph of a permutation tuple. It makes no reference to
  unitary representations, and it is a statement about all trivial words, not one fixed relation.

A refutation of (P2) is a sofic approximation of `K`. A proof of (P2) must use that `K` is
specific: it fails for every amenable infinite simple group, by the Folner calibration of
`kazhdan-consistent-partial-models-round-to-finite-actions`. What it must repair is monodromy at
filling radius `>~ log(1/eps)`. In particular, deleting a bounded neighbourhood of the relator
defects does not repair a marked solution (item 3).

## Attempts

1. **Common fixed points, Kazhdan rounding and the simple-group limit kernel (2026-09-17).** See
   route `titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair-proof`, kept in place as the
   attempt. It is currently OPEN because its prerequisites
   `kazhdan-consistent-partial-models-round-to-finite-actions` and
   `kazhdan-sofic-models-carry-long-scale-monodromy` were themselves returned to OPEN. It must not
   be read as re-establishing this claim once they recover: withdraw or correct it first. It requires
   `kazhdan-consistent-partial-models-round-to-finite-actions`,
   `kazhdan-sofic-models-carry-long-scale-monodromy`,
   `infinite-simple-group-permutation-stable-iff-nonsofic` and
   `titz-witzel-simple-kazhdan-cat0-lattices-exist`. Audit 2026-09-17: referee lenses 1 and 2
   returned *refuted*. Reasons, verbatim:

   * **Lens 1.** The numbered items 1 and 2 hold up. (DR1) is (CP1) of kazhdan-consistent-partial-models-round-to-finite-actions applied to the best consistent set, with the same hypotheses: K has no finite quotients and kappa is in the (KP) convention. I checked the CP1 proof, and its constants add up. In item 2: (a)=>(d) correctly uses 1=>2 of infinite-simple-group-permutation-stable-iff-nonsofic, since phi_j(g)=sigma_j(w_g) is an almost homomorphism on the countable simple group K. (c)=>(b) holds because common fixed points form a consistent set. (b)=>(c) is DR1. (c)=>(a) builds an almost solution from a sofic approximation using prefix triangle inequalities. The Titz Mite--Witzel import checks against arXiv:2509.05054v2 (Theorem A, Corollary B, and Gamma_1^2 being its own finite residual). So K is simple, Kazhdan and finitely presented. The claim still fails at the first step that does not follow, in proof section 4, 'The remarks on (P2)'. The statement says a proof of (P2) 'must use that K is specific: it fails for every amenable infinite simple group, by the Folner calibration', and section 4 justifies this only by citing that calibration. The calibration does not say this. It gives Folner models that are consistent on sets of density 1-|S|eta with eta->0, while generators move. That shows (CP1)/(DR1), that is (P1) or (b)=>(c), fails without (T). It gives no almost solution whose deficit stays bounded below, so it says nothing against deletion repair (P2). The Folner models actually satisfy the repair property. The cited result is also stated for finitely generated groups, while (P2) is defined through finite presentations, and no finitely presented infinite simple amenable group is known. A second defect is item 3's sentence 'The open trivial words live at filling radius of order log(1/eps_j)'. It cites item 2 of kazhdan-sofic-models-carry-long-scale-monodromy, which only proves that some open trivial word exists with rho(w) > R_0 when (LS1) holds. That is a lower bound for one word. There is no upper bound, and nothing about all open words: relators already fail to close at bad points at bounded filling radius. The core equivalence survives, but the node as written includes an imported claim that its source does not state, so I refute it.
   * **Lens 2.** The main mathematics holds. I checked the proof and every prerequisite in /home/user/ga-audit-main/research. Item 1 (DR1) is (CP1) from kazhdan-consistent-partial-models-round-to-finite-actions. I re-derived that proof: consistency makes theta_g a partial bijection via the reversed-path argument, the partial action globalizes, the Kazhdan projection gives (KP2), and with no finite quotients the count is eta + 2eta/kappa^2 + eta. Items 2 and 3 are also sound. (a)=>(d) uses simplicity through infinite-simple-group-permutation-stable-iff-nonsofic (1=>2), which carries a PASS review. (c)=>(b) uses common fixed points, (b)=>(c) is DR1, and (c)=>(a) builds an almost solution from a sofic approximation. The deficit bound c_kappa*m and the claim that deleting a bounded neighbourhood of the defects does not repair a marked solution both follow from (LS1). K is finitely presented, infinite, simple and Kazhdan by the Titz Mite--Witzel citation. It fails on the calibration lens. The claim body says, and proof section 4 'justifies', that any proof of (P2), deletion repair, must use that K is specific, because (P2) 'fails for every amenable infinite simple group, by the Folner calibration'. That is not what the cited calibration shows. In kazhdan-consistent-partial-models-round-to-finite-actions, the Folner models have consistent sets of density at least 1 - |S|eta. So they have eta(sigma) -> 0: they satisfy deletion repair (b), while their generators still move almost every point. What they break is (b)=>(c), i.e. the rounding step (P1) where property (T) is used, not (P2). Proof section 4 gives no argument that (P2) fails for any amenable group. I also expect (P2) to hold for amenable groups, since quasi-tiling interiors of almost actions give nearly full consistent sets. Separately, (P2) is only defined for finitely presented groups, and I don't know of any finitely presented infinite simple amenable group, so the non-example as stated may not exist. The node therefore puts its non-example on the wrong prerequisite and mislabels the step where the true case separates from it. A smaller overreach: item 3 says the open trivial words live at filling radius 'of order log(1/eps_j)', but kazhdan-sofic-models-carry-long-scale-monodromy proves only a lower bound. The core equivalence would survive once these remarks are corrected.
