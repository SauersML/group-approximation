---
rg: 2
id: leavitt-central-cover-nonsofic-proof
kind: route
title: Lift the Kazhdan infranormal compression obstruction through an arbitrary central cover
target: leavitt-all-countable-central-covers-are-nonsofic
requires: []
artifacts:
  - notes/NOTEPAD.md
---

The complete argument is recorded under **Kazhdan universal covers make every
Leavitt central cover nonsofic** in `notes/NOTEPAD.md`. Here is the proof
surface.

Let `Gamma < G` be the perfect infranormal pair in the rank-four Leavitt
compression configuration. Its universal central extensions `U_G -> G` and
`U_Gamma -> Gamma` have property `(T)`: after the established Leavitt rank
identifications they are Steinberg groups, and Ershov--Jaikin-Zapirain gives
property `(T)` for `St_n(R)` when `R` is finitely generated and `n >= 3`.

Given a central extension `p:E -> Q`, universality lifts the copy of `G` to a
perfect Kazhdan image `Ghat < E` and the core to a perfect Kazhdan subgroup
`Gammahat < Ghat`. Functoriality of universal central extensions lifts every
compressor of `Gamma`; because the lifted compressors generate `Ghat` modulo a
central subgroup and `Ghat` is perfect, they generate all of `Ghat`.
Therefore `Gammahat < Ghat` is still infranormal.

Choose the complementary-corner element `a` and a lift `ahat in E`. Since
`a` centralizes `Gamma`, each commutator `[ahat,x]`, `x in Gammahat`, lies in
`ker p`. Centrality of the kernel makes `x |-> [ahat,x]` a homomorphism from
the perfect group `Gammahat` to an abelian group, hence it is trivial. Thus
`ahat` centralizes `Gammahat` exactly.

If `E` were sofic, Kun--Thom centralizer normalization for the Kazhdan
infranormal pair `Gammahat < Ghat` would force the conjugate of `ahat` by the
lifted compressor to centralize the appropriate lifted core element. But the
resulting commutator projects under `p` to the explicit nontrivial
complementary-corner commutator in `Q`. Faithfulness of a sofic embedding is
contradicted. Hence `E` is nonsofic.

For `Q=EL_4(L_(F_2)(1,2))`, all inputs above are the kernel-checked rank-three
and rank-four compression configuration, Leavitt rank equivalence,
Kervaire--Steinberg universality, and the cited Steinberg property `(T)`
theorem. No finiteness assumption on the unstable `K_2` kernel is used.
