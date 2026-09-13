---
rg: 2
id: operator-mf-group-not-weakly-quasidiagonal-exists
kind: claim
title: Operator MF does not imply weak quasidiagonality for countable groups
distinct_from:
  mf-to-weak-qd-citation-has-unproved-lifting-step: that audit shows the printed passage from MF to weak quasidiagonality is unproved, and exhibits an MF witness of C_2 with no positive extension; this shows the implication itself is false for a specific group.
  weak-qd-kazhdan-quotientless-group-is-trivial: that is the Ozawa--Thom consequence for weakly quasidiagonal Kazhdan groups; this uses it as the tool to rule out weak quasidiagonality.
artifacts:
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
  - research/artifacts/ex-pestov91-second-review-2026-09-13.md
  - research/artifacts/pestov-9-1-writeup-2026-09-13-part3.md
---

There is a finitely generated group which is LEF, hence operator MF (it embeds in the unitary
group of `prod_n M_(k_n) / sum_n M_(k_n)`), but which is not weakly quasidiagonal: it admits no
asymptotically multiplicative sequence of unital completely positive maps `C*(G) -> M_(d_n)`
separating the points of `G`.

The witness is `G = EL_3(LC(X,F_q) ⋊ Z)` for an infinite minimal subshift `X`.

So the introductory arrow "MF implies weakly quasidiagonal" of Dadarlat, arXiv:2007.12655v2, is
false as a statement about groups. The completely positive hypothesis in Proposition 3.19
(Ozawa--Thom) cannot be replaced by operator MF, or even by LEF. The simple quotient `S = G/Z(G)` is a
second witness.

**Precise scope (2026-09-13, from the PDF and the e-print source).** PDF p. 2 prints: "It is clear from definitions
that MF ⇒ weak quasidiagonality and matricial stability ⇒ weak matricial stability."
- **Refuted:** only the first clause, "MF ⇒ weak quasidiagonality".
- **Correct:** the second clause. The polar parts of a ucp asymptotic homomorphism form a unitary one, and
  matricial stability gives nearby genuine representations.
- **Correct:** Proposition 3.19 (Ozawa--Thom, p. 10). Its proof was re-checked step by step
  (`research/artifacts/ex-pestov91-second-review-2026-09-13.md` §C; write-up Part 3 §8). It is what rules out weak
  quasidiagonality here. Example 3.15(ii) (p. 9) is correct for the same reason.
- **What the definitions give:** the converse arrow, weak quasidiagonality ⇒ MF, by polar decomposition.
- **The paper's main theorems do not use the clause.** Theorem 1.1 follows from Theorem 1.2 through Lemma 3.17(i)
  (a matricially stable MF group is MAP), Remark 3.5(i) (MAP groups are quasidiagonal) and "Quasidiagonal groups
  are weakly quasidiagonal" (p. 2). The rest of the paper was not audited.
