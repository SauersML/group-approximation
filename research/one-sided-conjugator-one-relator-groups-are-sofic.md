---
rg: 2
id: one-sided-conjugator-one-relator-groups-are-sofic
kind: claim
title: One-sided indexed conjugators give sofic one-relator groups
distinct_from:
  one-relator-groups-sofic: This assumes an explicit one-sided form of the conjugator in a Baumslag-type relation; that asks for all defining relators.
  triangular-conjugate-bs-chains-are-sofic: That proves soficity of an indexed kernel; this identifies a two-generator one-relator group with a cyclic extension of such a kernel.
artifacts:
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
---

Write `a_j=b^(-j)ab^j` in the free group `F(a,b)`. Let `d>0`, let `V` be
any finite word in `a_j^(+/-1)` for strictly positive `j`, and put `w=b^d V`.
For all nonzero integers `l,k`, the one-relator group

    G(a,w;l,k) = <a,b | (a^l)^(a^w)=a^k>

is sofic, with conjugation convention `x^y=y^(-1)xy`.

Replacing `b` by `b^(-1)` gives the corresponding strictly negative-index
family. The empty word `V` is allowed.

In particular `w=b^(-1)ab^2=b a_2` satisfies the hypotheses.
The proof is written mathematics using standard permanence results, not a
Lean-certified theorem and not a solution for every one-relator group.
