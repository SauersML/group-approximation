---
rg: 2
id: independent-set-injection-splits-as-question-bijection
kind: claim
title: A perfect independent-set model on a game graph is a quantum bijection of question labels times a perfect model of the source game
distinct_from:
  synchronous-independent-set-reduction-preserves-a-quadratic-gap: that is the quantitative soundness transfer of the independent-set reduction; this is the exact parametrization of all perfect tracial models, and it locates the non-square part of the quantum injection in the source game's answers.
  closure-safe-support-is-exactly-the-colored-iso-rung: that characterizes the bisynchronous gaps feeding the colored rung and notes that independent-set games fail squareness; this shows that the question half of that injection is already a quantum bijection, so the missing square completion is the source game's own.
  perfect-qc-separation-yields-finite-bcs-with-no-matrix-model: that extracts from Lin and Mancinska--Spaas--Spirig--Vernooij an independent-set algebra with a trace and no matrix model; this describes every perfect tracial model of such an algebra.
---

**ESTABLISHED** by `independent-set-injection-splits-as-question-bijection-proof`.
Not reviewed by an ex-verify lane.

**Setup.**

- `G = (Q, A, V)` is a finite synchronous game: `V(q,q;a,a') = 0` for
  `a != a'`.  Answers with `V(q,q;a,a) = 0` are deleted, since every perfect
  model assigns them projection zero.
- `X(G)` is the game graph of Mančinska--Roberson--Varvitsiotis, as in
  Mančinska--Spaas--Spirig--Vernooij (MSSV), arXiv:2505.05253, §1 and
  Definition 2.7.  Its vertices are the pairs `(q,a)`, and two distinct
  vertices are adjacent iff `V(q,q';a,a') = 0` or `V(q',q;a',a) = 0`.
- `I` is the `t`-independent-set game on `X(G)` with `t = |Q|`.  Questions
  `[t]`; equal questions need equal answers, distinct questions need distinct
  non-adjacent answers.
- A *perfect tracial model* of a synchronous game is a family of PVMs in a
  tracial von Neumann algebra `(M, tau)` with faithful normal trace, whose
  forbidden pairs have product zero (MSSV (2.1) and footnote 8).

**Theorem.**

- **(IS1)** Let `(P_i^v)`, `i in [t]`, `v in V(X(G))`, be a perfect tracial
  model of `I`.  Put

  ```text
  W_(iq) = sum_a P_i^(q,a),        P_q^a = sum_i P_i^(q,a).
  ```

  Then `W = (W_(iq))` is a `t x |Q|` magic unitary, `(P_q^a)` is a perfect
  tracial model of `G`, and

  ```text
  P_i^(q,a) = W_(iq) P_q^a = P_q^a W_(iq).                        (ISB1)
  ```

- **(IS2)** Conversely, let `(P_q^a)` be a perfect tracial model of `G` and
  `W` a `t x |Q|` magic unitary in the same algebra with
  `[W_(iq), P_q^a] = 0` for all `i, q, a`.  Then `P_i^(q,a) = W_(iq) P_q^a`
  is a perfect tracial model of `I`.
- **(IS3)** `I` has a perfect model in `R^U` iff `G` has one.  Take `W = 1`
  after labelling `[t] = Q` for one direction, and (IS1) inside `R^U` for the
  other.

**What this says about completing the injection.**

- A perfect strategy for `I` is a quantum injection `[t] -> Q x A`.  By (ISB1)
  it factors into a quantum bijection `W: [t] -> Q` of question labels,
  followed by the answer PVMs of `G`.  `W` commutes with the answers of its
  own question and is otherwise free.
- So the squareness defect of the injection, `|Q|(|A|-1)` columns, sits
  entirely in the answer coordinate of the source game.  The question half is
  already square.
- **The completion problem, restated.**  Completing the injection of `I` to a
  quantum bijection, the open step named in
  `closure-safe-support-is-exactly-the-colored-iso-rung`, is the same problem
  as presenting the source game `G` by a square game whose perfect support is
  closure-safe.
  - The independent-set conversion gains closure safety for free.
  - It adds only a relabelling of questions, which is already square.
  - It does not move the source any closer to a bijection.

**Credit.**

- The operators `P_q^a`, and the proof that they form a perfect model of `G`,
  are the second half of the proof of MSSV Theorem 3.1 (due to MRV15).  They
  were read at source in the arXiv text fetched on 2026-09-13.  That proof
  works in a tracial von Neumann algebra, so it covers both commuting-operator
  and `R^U` models.
- The magic unitary `W`, the factorization (ISB1) and the converse (IS2) are
  small additions to that proof.  A full-text read of MSSV §3 found none of
  the three.  The check is bounded to that paper.
