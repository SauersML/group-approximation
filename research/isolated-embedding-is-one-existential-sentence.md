---
rg: 2
id: isolated-embedding-is-one-existential-sentence
kind: claim
title: An isolated group embeds in a group S exactly when S satisfies one existential sentence built from a finite presentation and a finite discriminating subset
distinct_from:
  fp-simple-groups-are-isolated: that places finitely presented simple groups among the isolated groups; this shows that for any isolated group, embeddability into a host is a single existential first-order property of the host.
  every-decidable-group-embeds-in-an-isolated-group: that is the open question of Cornulier--Guyot--Pitsch whether every decidable group has an isolated overgroup; this is an elementary theorem about what embedding an isolated group into a host means.
  outer-extensions-of-fp-simple-groups-are-isolated: that supplies a class of isolated groups; this applies to every isolated group.
---

**ESTABLISHED** through `isolated-embedding-is-one-existential-sentence-proof`
(elementary).

Terms as in `fp-simple-groups-are-isolated`, from Cornulier--Guyot--Pitsch,
arXiv:math/0511714 (TeX source `CoGuPi8.tex`, fetched 2026-09-17 from
`https://arxiv.org/e-print/math/0511714`; line numbers refer to that file).
- Finitely discriminable (Proposition--Definition, lines 519–533), condition
  iii): "There exists a finite {\em discriminating subset} in $G$: this is a
  finite subset $F \subset G-\{1\}$ such that any non-trivial normal subgroup
  of $G$ contains at least one element of $F$."
- Isolated (Proposition `propcar`, lines 554–557): "A group $G$ is isolated if
  and only if it is both finitely presentable and finitely discriminable."

**Statement.** Let `H` be an isolated group. Fix a finite presentation
`H = ⟨x_1, ..., x_n | r_1, ..., r_d⟩` and a finite discriminating subset
`F = {f_1, ..., f_k}` of `H`, each `f_i` written as a word `f_i(x)`. Let `Σ_H`
be the existential sentence

`∃ y_1 ... y_n ( r_1(y) = 1 ∧ ... ∧ r_d(y) = 1 ∧ f_1(y) ≠ 1 ∧ ... ∧ f_k(y) ≠ 1 )`.

Then for every group `S`: `H` embeds in `S` iff `S ⊨ Σ_H`.

**Consequences.**
1. For a class `K` of groups, `H` embeds in a member of `K` iff `Σ_H` holds in
   some member of `K`. So `H` embeds in no member of `K` iff the universal
   sentence `¬Σ_H` belongs to the universal theory `Th_∀(K)`.
2. If `H` satisfies every universal sentence (without constants) true in all
   members of `K`, then `H` embeds in a member of `K`. The converse holds
   because universal sentences pass to subgroups. In marked-group language,
   an isolated group lies in the closure of the finitely generated subgroups of
   members of `K` iff it is one of them.

**Novelty.** None for the statement. CGP (lines 781–784) attribute to
[MR0414671, Lemma 2.4] the observation "a given isolated group embeds in every
existentially closed group", which is the case where `S` is existentially
closed. The node exists as the lemma behind `boone-higman-iff-isolated-hosts-and-local-boone-higman`.
