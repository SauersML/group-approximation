---
rg: 2
id: thompson-t-disjoint-pair-cstar-simple-subgroup-criterion
kind: claim
title: A C*-simple subgroup of Thompson's group T containing two disjointly supported elements forces F to be non-amenable
distinct_from:
  thompson-f-not-amenable-iff-thompson-t-cstar-simple: that is the imported equivalence for T itself; this is a criterion for arbitrary subgroups of T, needing only one disjointly supported pair inside a C*-simple subgroup.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that is about Følner sets in Schreier graphs; this is about the reduced C*-algebras of subgroups of T.
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md
---

**ESTABLISHED.** Let `H` be a subgroup of Thompson's group `T` containing nontrivial
elements `a, b` with disjoint supports on the circle, i.e. every point is fixed by `a` or by
`b`. If `C*_r(H)` is simple, then `F` is not amenable.

**Converse.** If `F` is not amenable, `T` itself is such a subgroup. It is C*-simple by
`thompson-f-not-amenable-iff-thompson-t-cstar-simple`, and it contains disjointly supported
bumps. So non-amenability of `F` is equivalent to the existence of a C*-simple subgroup of `T`
containing a disjoint pair (`thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`).

**Mechanism.**
- `x = 1 − λ(a) − λ(b) + λ(ab)` is a nonzero element of `C[H]`.
- `x` acts as `0` in the quasi-regular representation of `T` on the dyadic orbit of `0`,
  whose point stabilizer is `F`: at every point one of `a, b` acts trivially.
- If `F` were amenable, that representation would be weakly contained in `λ_T` and would
  restrict to a nonzero, hence faithful, representation of the simple algebra `C*_r(H)`
  killing `x`.

**Credit and scope.** For `H = T` and one specific disjoint pair this is exactly the proof of
Haagerup–Olesen, arXiv:1609.05086, Theorem 4.5. Its outline was read from the LaTeX source,
lines 814–891: the quasi-regular representation is weakly contained in the regular one, and
`π(a + b − ab − e) = 0`. The same theorem was re-obtained by Breuillard–Kalantar–Kennedy–Ozawa.
The extension to arbitrary subgroups `H` is recorded here as an unreviewed proof. It is a
small step, and no novelty is claimed. What it adds is a local certificate target. The
standard inputs, not re-read, are:
- Fell continuity of induction;
- `Ind_F^T λ_F = λ_T`;
- the isometric inclusion `C*_r(H) ⊆ C*_r(T)`.

Proof route: `thompson-t-disjoint-pair-cstar-simple-subgroup-criterion-proof`.
