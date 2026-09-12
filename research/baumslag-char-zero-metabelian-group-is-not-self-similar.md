---
rg: 2
id: baumslag-char-zero-metabelian-group-is-not-self-similar
kind: claim
title: Baumslag's torsion-free finitely presented metabelian group has no faithful state-closed action on any regular rooted tree
distinct_from:
  affine-self-similar-coordinate-rings-are-one-dimensional: that obstructs affine digit actions over coordinate rings of positive transcendence degree; this obstructs every faithful state-closed action of one particular metabelian group, affine or not, transitive on the first level or not.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's theorem for finitely presented self-similar inputs; this shows that Baumslag's characteristic-zero group, although finitely presented, is not such an input itself.
artifacts:
  - research/artifacts/bh-baumslag-char0-metabelian-2026-09-12.md
---

**ESTABLISHED.** Let

```text
B = < a, s, t | [s,t], [a, a^t], a^s = a a^t >  =  R x| P,
R = Z[x, x^-1, (1+x)^-1],   P = Z^2 = <s,t>,   s.r = (1+x) r,   t.r = x r,
```

Baumslag's finitely presented metabelian group with free abelian derived
subgroup of infinite rank. Then `B` is **not self-similar**. For every `d >= 2`,
every homomorphism `B -> Aut(T_d)` whose image is state-closed (all sections of
all elements lie in the image, which is Zaremsky's definition in
arXiv:2405.09722v2) has nontrivial kernel. No transitivity on the first level is
assumed.

**Proof shape.** A faithful state-closed action gives finitely many virtual
endomorphisms `f_i : H_i -> B`, with `[B:H_i]` finite, whose joint core (the
largest normal subgroup inside every `H_i` mapped into itself by every `f_i`)
is trivial. Every nontrivial normal subgroup of `B` meets `R` in a nonzero
ideal. Each `f_i` either kills a nonzero ideal of `R`, or restricts on
`H_i ∩ R` to `r -> lambda sigma(r)` with `lambda in R` and `sigma` one of the
six ring automorphisms of `R`. A nonzero `Aut(R)`-stable ideal inside all the
`H_i` and all the kernels therefore lies in the joint core. The details are in
`baumslag-char-zero-metabelian-not-self-similar-proof`.

**Why `Z wr Z` behaves differently.** Dantas--Santos--Sidki
(arXiv:2004.08941) give a faithful intransitive state-closed action of
`Z wr Z = Z[t^±1] x| Z`. There the finite-index sublattice `mZ` sees
`Q(t)` only as a degree-`m` extension of `Q(t^m)`, so decimation maps
`sum c_k t^k -> sum c_(mk) t^k` are twisted module maps that contract. For `B`
the support of `R` is the curve `s = 1 + t` in the 2-torus. Restricting to any
finite-index sublattice is birational on that curve, so every twisted module map
is a unit multiple of a curve symmetry and nothing contracts.

## Consequences and scope

- Zaremsky's Theorem 1.1 cannot be applied to `B` itself, even though `B` is
  finitely presented.
- **Relation to the Krull-dimension remark.** Kochloukova--Sidki
  (arXiv:1710.04745, after Theorem C) note that, by Dantas--Sidki, their
  Krull-dimension-one theorem fails in higher Krull dimension. The witness is
  `Z wr Z`, which has no faithful transitive action coming from a single virtual
  endomorphism, yet has a faithful intransitive one (Dantas--Santos--Sidki).
  For `B` the failure persists for all actions, intransitive included.
- **Not excluded:** embeddings of `B` into a *larger* finitely presented
  self-similar group. Every subgroup of such a group satisfies Boone--Higman.
  So `baumslag-char-zero-metabelian-group-satisfies-boone-higman` stays OPEN.
- **Not excluded:** faithful actions on locally finite rooted trees that are not
  state-closed. `B` is residually finite, and its `p`-adic affine action through
  a transcendental `p`-adic point is faithful but not state-closed.

No novelty is claimed. The sources checked (the abstract and Proposition A of
Dantas--Santos--Sidki, Theorem C and Section 7 of Kochloukova--Sidki) state no
such result for `B`.
