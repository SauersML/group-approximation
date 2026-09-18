---
rg: 2
id: fg-complex-linear-groups-are-quasi-retracts-of-simple-groups
kind: claim
title: Every finitely generated subgroup of GL_n(C) is a subgroup and a quasi-retract of a simple group with the same finiteness properties
distinct_from:
  linear-groups-over-q-are-quasi-retracts-of-simple-groups: that is LISW Theorem 1.4 for subgroups of GL_n(Q) (literature import); this is their Question 1.10, the same statement over C.
  fg-linear-groups-embed-in-fp-self-similar-groups: that gives a finitely presented self-similar host with no control of finiteness properties or coarse geometry; this asks for a simple host with the same finiteness properties and a quasi-retract.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN.** Printed as Question 1.10 of Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1
(TeX label `quest:linear-groups-as-retracts`, l.289–297):

> Let H be a finitely generated subgroup of GL_n(C) for some n ∈ N. Does there exist
> a simple group G that has the following properties? (1) G has the same finiteness
> properties as H, (2) H is a subgroup of G, (3) G admits a quasi-retract onto H.

The authors add: "an answer to this question will likely require completely new
techniques" (l.299).

**Lead on main (lane remark, not a proof).** `fg-linear-groups-embed-in-fp-self-similar-groups`
puts `H` in a finitely presented self-similar affine group over
`Z[1/m][s_1,…,s_k]`, whose Röver–Nekrashevych commutator subgroup is finitely
presented and simple (Zaremsky, arXiv:2405.09722, Theorem 1.1). What is missing is
(1) matching finiteness properties below type `F_2` and above it, and (3) a
quasi-retract: the transcendental coordinates `s_j` enter the host, and LISW's
Theorem 1.4 construction retracts only onto the split extension of `H` over `Q`.
