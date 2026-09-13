---
rg: 2
id: sofic-coset-actions-pass-to-marked-colimits
kind: claim
title: Sofic coset actions pass to stabilizer unions and directed colimits, so colimits of separable pairs give sofic actions without exact models
distinct_from:
  gkp-sofic-action-toolkit: that is GKP permanence in the acting group (restriction, orbits, increasing unions of the acting group, locally finite stabilizers); this is permanence along the stabilizer and along quotient limits of the whole pair, with the exact-atlas criterion for separable stabilizers and the finite-presentation stop
  codense-kazhdan-coset-action-forces-permutation-outliers: that excludes exact and correctable atlases for a co-dense Kazhdan pair; this manufactures atlases that are exact for approximating pairs and only approximate for the limit pair, and proves the manufacture is impossible when the host is finitely presented and the stabilizer finitely generated
---

**ESTABLISHED** (complete handwritten proof in the route; unreviewed).
"Sofic action" is Gao--Kunnawalkam Elayavalli--Patchell Definition 2.1(5),
with orbit approximations as in their Definition 2.1(3) (verbatim in
`research/artifacts/kun-thom-2608-06222-verified.md`).  All groups are
countable.

1. **Separable stabilizers.**  If `H` is closed in the profinite topology
   of `G`, then `G action G/H` is sofic, witnessed by genuine finite actions
   `G -> Sym(G/N)` with exact atlases and error zero.

2. **Stabilizer unions.**  If `H_1 <= H_2 <= ...` are subgroups of `G` with
   union `H`, and every `G action G/H_n` is sofic, then `G action G/H` is
   sofic.

3. **Directed colimits of pairs.**  Let `q_n: G_n -> G_(n+1)` be
   homomorphisms and `p_n: G_n -> G` surjections with `p_(n+1) q_n = p_n`,
   such that every element of `ker p_n` is killed by `q_(m-1)...q_n` for some
   `m`.  Let `H_n <= G_n` satisfy `q_n(H_n) <= H_(n+1)`, `p_n(H_n) <= H`, and
   `H = union_n p_n(H_n)`.  If every `G_n action G_n/H_n` is sofic, then
   `G action G/H` is sofic.  Item 2 is the case `G_n=G`, `p_n=q_n=id`.

4. **Colimit criterion.**  In item 3, if every `H_n` is separable in `G_n`,
   then `G action G/H` is sofic.  No separability of `H` in `G` is needed.
   The resulting atlases are exact finite actions of `G_n` that are only
   approximately multiplicative for `G`.  This is a source of the
   "labelled models that cannot be corrected to exact actions" demanded by
   `codense-kazhdan-coset-action-forces-permutation-outliers` and
   `codense-tau-coset-soficity-forces-permutation-instability`.

5. **Finite-presentation stop.**  If `G` is finitely presented, `H` is
   finitely generated, and the data of item 4 exist, then `H` is separable
   in `G`.  Consequently a co-dense pair (where `HN=G` for every finite-index
   normal `N`, so `H` is not separable) with finitely presented host and
   finitely generated stabilizer admits no colimit presentation by separable
   pairs.  Its sofic models, if any, are genuinely approximate.

6. **Closure in the space of marked pairs.**  Fix a free group `F` on a
   countable set.  A marked pair is `(N,M)` with `N <| F` and `N <= M <= F`;
   it defines `F/N action F/M`.  Give marked pairs the topology of pointwise
   convergence of the indicator functions of `N` and `M` on `F`.  The set of
   marked pairs whose coset action is sofic is closed.  Items 2 and 3 are
   special cases.

7. **LEF pairs.**  Call `(G,H)` an LEF pair if its marked pair is a limit of
   marked pairs `(N_k,M_k)` with `F/N_k` finite.  An LEF pair has a sofic
   coset action whose window models are genuine actions of finite groups
   with error zero.  If `G` is finitely presented and `H` finitely
   generated, then `(G,H)` is an LEF pair if and only if `G` is residually
   finite and `H` is separable in `G`.  So item 5 is the finitely presented
   case of this dichotomy, and for such pairs co-density excludes LEF.

## Consequences for the Hecke pairs

- `C=SL_3(F_2[t])` is Kazhdan, hence finitely generated, and co-dense in
  `Lambda=SL_3(F_2[t,1/t])` (`function-field-hecke-pair-is-perfect-codense-kazhdan`).
  So item 5 blocks item 4 for `C < Lambda` whenever `Lambda` is finitely
  presented.  The rank-two positive side must then be a non-correctable
  almost-action, as the permutation-instability nodes already say.
- The rank-one corner `SL_2(F_2[t]) < SL_2(F_2[t,1/t])` escapes item 5 on the
  stabilizer side: `SL_2(F_2[t]) = GL_2(F_2) *_(B(F_2)) B(F_2[t])`
  (`polynomial-gl2-over-a-field-is-a-nontrivial-amalgam`, with `GL_2=SL_2`
  over `F_2[t]`) is not finitely generated.  This is the lane's route into
  the rank-one function-field vertex action.

## Model test

- Hypotheses are not vacuous and not automatic: `H_n = {1}` recovers the
  known fact that marked limits of sofic groups are sofic, while the
  Kun--Thom action `coordinate-action-not-sofic` shows that the conclusion
  fails for some pairs, so no pair presentation of that action by sofic
  approximants exists.
- Item 5 is sharp in form: `H` finitely generated is used to push all of
  `H` into one `H_n`; with `H` infinitely generated the section need not
  carry `H` into any single `H_n`.

DERIVATION
sofic-coset-actions-pass-to-marked-colimits-proof
