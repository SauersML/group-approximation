---
rg: 2
id: boone-higman-iff-isolated-hosts-and-local-boone-higman-proof
kind: route
title: Finitely presented simple groups are isolated; conversely an isolated overgroup is caught by one existential sentence, which Local Boone--Higman realizes in a finitely presented simple group
target: boone-higman-iff-isolated-hosts-and-local-boone-higman
requires: [isolated-embedding-is-one-existential-sentence, fp-simple-groups-are-isolated]
---

Imported, verbatim, from Cornulier--Guyot--Pitsch arXiv:math/0511714 (TeX source
`CoGuPi8.tex`, fetched 2026-09-17 from `https://arxiv.org/e-print/math/0511714`),
Corollary at lines 704–706: "An isolated group has solvable word problem."

Standard fact used: a finitely generated subgroup of a finitely generated group
with solvable word problem has solvable word problem. Rewrite its generators as
words in the ambient generators and run the ambient algorithm.

**(1) ⇒ (2), first half.** Let `G` be finitely generated with solvable word
problem. By (1), `G ≤ S` with `S` finitely presented and simple. By
`fp-simple-groups-are-isolated`, `S` is isolated.

**(1) ⇒ (2), second half.** Suppose the system `u_i(y) = 1, v_j(y) ≠ 1` has a
solution `g` in a finitely generated group `G` with solvable word problem. By
(1), `G ≤ S` with `S` finitely presented simple. The words `u_i(g)` and `v_j(g)`
have the same values in `G` and in `S`, so `g` is a solution in `S`.

**(2) ⇒ (1).** Let `G` be finitely generated with solvable word problem.
- By CGP Question 4 (first half of (2)), `G ≤ H` with `H` isolated.
- Fix a finite presentation `⟨x_1, ..., x_n | r_1, ..., r_d⟩` of `H` and a finite
  discriminating subset `F = {f_1, ..., f_k}`. Consider the system
  `r_i(y) = 1, f_j(y) ≠ 1`. It has the solution `y = x` in `H`.
- `H` is finitely generated and, by the imported corollary, has solvable word
  problem. So Local Boone--Higman (second half of (2)) gives a solution in some
  finitely presented simple group `S`. That is, `S ⊨ Σ_H`.
- By `isolated-embedding-is-one-existential-sentence`, `H` embeds in `S`, hence
  so does `G`.

**Per-input form.** For isolated `H`, the target's first equivalence is the
lemma applied to each finitely presented simple group. The second is the lemma's
Consequence 2 with `K = fps`.

**Counterexample reading.** If `G ≤ H` and `H ≤ S`, then `G ≤ S`. So when `G`
fails (1), every isolated overgroup `H` of `G` fails (1). By the per-input form,
`¬Σ_H` holds in all finitely presented simple groups. It fails in `H`, witnessed
by `x`. `∎`
