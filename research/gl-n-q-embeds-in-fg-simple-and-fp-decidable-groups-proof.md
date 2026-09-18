---
rg: 2
id: gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups-proof
kind: route
title: Higman--Neumann--Neumann two-generator overgroup, then Clapham, Belk--Zaremsky and Higman
target: gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups
requires:
  - clapham-fp-embedding-preserves-word-problem
  - boone-higman-thompson-simple-envelope
---

All quotations are from Belk--Bleak--Matucci--Zaremsky, *Progress around the
Boone--Higman conjecture*, arXiv:2306.16356v3.

**Item (1).** `GL_n(Q)` has a solvable word problem for its standard
enumerated generating set. Proof of Proposition 3.3: "For statement (2), it it
easy to enumerate a generating set for GL_n(Q), and the word problem is
solvable by direct matrix computations." The same proof: "the
Higman--Neumann--Neuman construction in [HNN] embeds every countable group with
a solvable word problem into a two-generated group with solvable word
problem." Call that group `G*`. (For `n = 1` the same sentences apply to the
countable abelian group `Q^x`.)

**Item (2).** Apply `clapham-fp-embedding-preserves-word-problem` to `G*`. This
is also Proposition 3.3(2) verbatim: "Furthermore, the following groups can be
embedded into finitely presented groups with solvable word problem: ... (2) The
group GL_n(Q) for all n >= 2."

**Item (3).** Theorem 4.13 (Belk--Zaremsky): "If G is a finitely generated
group then GV_G is a finitely generated simple group, and G embeds
isometrically into GV_G." The next sentence: "It is easy to see that GV_G has
solvable word problem if and only if G does." Apply it to `G*`. Alternatively,
apply `boone-higman-thompson-simple-envelope` (survey Theorem 3.8) to `G*`.

**Item (4).** A finitely generated group with solvable word problem is
computably presented (its set of trivial words is computable, hence computably
enumerable; survey Remark 2.3). By the Higman embedding theorem (survey §2)
the group `S = G* V_(G*)` of item (3) embeds in a finitely presented group `P`.
Then `GL_n(Q) <= G* <= S <= P` with `S` simple. This is the survey's
Corollary 3.7 argument, applied to the countable input through `G*`.
