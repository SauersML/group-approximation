---
rg: 2
id: kms-group-with-stop-relations-simulates-all-words-proof
kind: route
title: The KMS model satisfies the stop relations, Minsky chains carry zero words to the stop letter, and the basis argument goes through
target: kms-group-with-stop-relations-simulates-all-words
requires:
  - kms-minsky-machine-groups-simulate-their-machines
artifacts:
  - research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md
---

Page numbers refer to KMS arXiv:1204.6506v5, read from the PDF.

**Clause 1.**
- `G_0` is a quotient of `G`, and varieties are closed under quotients.
- The map of Lemma 4.10 sends `x_(q_0 w)` to `z_(1, q_0 w)`.  In `S(M)` we have `q_0 w = 0`, and
  `z_(1,0) = 1` (Lemma 4.9, p. 24).  So the map factors through `G_0`, and it is still onto
  (Lemma 4.11).

**Clause 2, "if".**
- *Nonzero elements.*  KMS prove Lemma 3.1 for `G(M)` (p. 22) by turning each commutativity or
  Minsky step between configuration-type words into a group equality.  This uses G1, G2, G8 and
  the permutation equalities (12).  All of those equalities survive in the quotient `G_0`.
- *Zero elements.*  Let `V = q_i a^m A^al` be `0` in `S(M)`.
  - Minsky relations map subwords of configuration words to such subwords, since they create or
    remove letters next to `q` and never put `a_n` after `A_n`.  So along a chain from `V`, no
    two-letter 0-subword appears, and the chain reaches `0` only by creating `q_0` through a
    Minsky relation into command `0`.
  - By the nonzero case, the group word of `V` equals `x_(q_0 A_0) * (letters)`.
  - That element is `1` in `G_0`: `1 * a_i = 1^(-1) 1^(a_i) (1^(a_i^(-1)))^(-1) 1^((a_i')^(-1)) = 1`
    and `1 * A_i = [1, A_i] = 1`.
  - So every word for a zero element is `1`, and any two of them are equal.

**Clause 2, "only if".**
- By clause 1, equal in `G_0` implies equal in `Ḡ`.
- In `Ḡ` the word of a nonzero element `u` of `S(M)` is the basis vector `z_(1,u)` (Lemma 4.9),
  and the word of `0` is `1`.
- Distinct nonzero elements give distinct basis vectors, and a basis vector is not `1`.  So
  `Ḡ`-equality forces `S(M)`-equality.  This is the argument of pp. 24--25, now with the zero
  element included.

**Clause 3.**
- *Definition and zero words.*  Lemma 4.11 defines `x_(i,w)`, `w in W cup W_0`:
  - `x_(1,u) = x_u` for `u in U`;
  - `x_(i,w) * a_j = x_(i, w a_j)` and `x_(i,w) * A_j = x_(i, w A_j)`;
  - the indices `i + e_j` and `i + 2 e_j` come from conjugating by `(a_j')^(-1)` and `a_j^(-1)`.

  By clause 2, `x_(1,w) = 1` whenever `w = 0` in `S(M)`.  By induction on the sum of `i`, then
  `x_(i,w) = 1` for every `i`.  For `w in W`, a zero element of `Š` carries `q_0`, and
  `x_(q_0) = 1` is among the added relations (`w = 1 in U_0`).
- *Spanning.*  The convention `x_(i,0) = 1` of Lemmas 4.12 and 4.15 is now a relation.
  - Lemma 4.12's proof shows that each `x_u^y` is a product of elements `x_(i',w')`: the
    conjugation formulas from G2, G5 c) and G6 match formula (13).
  - Where (13) produces `z_(i',0)`, the group element is `1` in `G_0`.
  - By Remark 4.7, the `x_u^y` generate `T`.  So the `x_(i,w)` with `w` nonzero span `T_0`.
- *Independence.*  Their images `z_(i,w)` are the basis of `T_1` (the independence half of
  Lemma 4.14).  So `T_0 -> T_1` is injective, hence an isomorphism.
