---
rg: 2
id: clifford-cover-cofinite-lamp-subgroups-contain-the-center
kind: claim
title: On complete-graph and induced-matching Clifford covers every subgroup with cofinite lamp part contains the center
distinct_from:
  kun-thom-clifford-cover-has-no-finitary-site-structure: that rules out normal site projections of the lamp group; this rules out the non-normal marked-site coset transplants, by showing every subgroup with cofinite lamp part contains eps.
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that proves the untwisted wreath W surjunctive by marked-site transplants and peeling; this shows those transplants collapse the center of a Clifford cover to W, so the peeling proof does not transfer.
artifacts:
  - research/artifacts/clifford-cover-phase-barrier-2026-09-12.md
---

**Setting.** `E_S = Vtilde_S semidirect G` is a Clifford cover over a `G`-set `X`, with adjacency form `b_S` on
`V = directSum_X F_2`. The *lamp part* of `H <= E_S` is `L_H = proj_V(H cap Vtilde_S)`.

**Lemma.** If `b_S` vanishes identically on no subspace of finite codimension, every subgroup whose lamp part
has finite codimension contains `eps`.

**Instances.**
- **The complete graph on an infinite set.** Three sites in one coset of `L_H` give `e_a + e_b` and `e_a + e_c`,
  whose form value is `1`.
- **Every graph with an infinite induced matching,** in particular every bounded-degree graph with infinitely
  many edges.

**Consequence.** The marked-site subgroups `H_(S,A_0)` of the lamp-wreath peeling proof have cofinite lamp part.
Their Clifford analogues all contain `eps`:
- their coset spaces are coset spaces of `W = E_S/<eps>`;
- transplanted configurations are `eps`-invariant;
- no family of them separates `1` from `eps`.

A separating subgroup has lamp part of infinite codimension, and the strata step, as written, needs finite lamp
data. So marked-site peeling reproves only bijectivity on `Fix(eps)` and does not settle surjunctivity of these
covers.

**ESTABLISHED** by `cofinite-lamp-subgroups-contain-center-proof` (artifact Section 2). Proved on paper by lane
w4-clifford-complete; independent re-derivation requested from w3-vf-nonlinear.
