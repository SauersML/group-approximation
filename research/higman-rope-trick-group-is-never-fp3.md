---
rg: 2
id: higman-rope-trick-group-is-never-fp3
kind: claim
title: "For infinite finitely generated G = F/R with R nontrivial, every Higman rope-trick group Hig_iota(G) fails to be of type FP_3(Q)"
invalidates:
  - type-fn-hosts-via-higman-rope-trick
artifacts:
  - research/artifacts/zp-review-topology-2026-09-13-part1.md
---

Fournier-Facio and Zaremsky, *Finiteness properties and Higman's rope trick*,
arXiv:2607.21727v1 (23 July 2026), Theorem B, verbatim: "Let G=F/R, and let
Hig_ι(G) be as in Definition 1.5. Suppose G is infinite and R≠1. Then
H₃(Hig_ι(G),ℚ) is infinite-dimensional; in particular Hig_ι(G) is not of type
FP₃(ℚ)."

**Setting (Definition 1.5).** `F` is a finitely generated free group, so
`G = F/R` is finitely generated. `L = F_1 *_R F_2` is the double of `F` along
`R`, `π: L -> G` kills `F_2`, and `ι: L -> P` embeds `L` in a finitely
generated group `P`. `Hig_ι(G)` is the HNN extension with vertex group `P x G`
and edge group `L`, conjugating `ι x 1` to `ι x π`. The conclusion holds for
every such `P` and `ι`.

A group of type `FP_3(Z)` is of type `FP_3(Q)`, and a group of type `F_3` is of
type `FP_3(Z)`. So `Hig_ι(G)` is never of type `FP_3`, `F_3` or `F_∞`.

**Consequences for Zaremsky Problem 1.1.** The rope trick is the device behind
Higman's embedding theorem and Leary's `FP_2` embeddings. Theorem B shows that
its container never goes above `FP_2`. This claim invalidates
`type-fn-hosts-via-higman-rope-trick`, the dead route that proposes the container
as an `F_{n+1}` host. It rules out a method, not every host, so it is not a
witness for `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`. The same
paper's Theorem A is `fournier-facio-zaremsky-rp-fp-n-hosts-give-f-n-hosts`.

**Provenance.** Theorem B, Definition 1.5 and the paper's title, authors and
date were read from the arXiv v1 HTML on 2026-09-13. An independent reading
agrees: `research/artifacts/zp-review-topology-2026-09-13-part1.md` §8d.
Correction note: the first version's title said "infinite one-relator-quotient",
which is wrong. `G` is any infinite finitely generated quotient `F/R` with
`R != 1`.
