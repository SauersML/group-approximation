---
rg: 2
id: bare-relative-wall-exists
kind: claim
title: One bare relative wall in a Connes-embeddable model
distinct_from:
  kun-thom-clifford-relative-wall: That claim demands the Clifford wall — the compressed lamp must anticommute with the lamp — and is stated as a finite normalized-Hilbert--Schmidt target; this one asks only that the two be different, which is strictly weaker and already sufficient for Q3.4.
  relative-wall-commutant-growth: That claim is the established equivalence between a wall and properness of a relative-commutant inclusion in an arbitrary finite tracial algebra; this one is the existence assertion in a Connes-embeddable one, which is the actual open problem.
  hyperlinear-wreath-model: That claim asks for microstates of the whole wreath candidate; this one asks for a single unitary in one relative commutant and needs no faithful model of any group.
  kt-centralizer-normalization-hs: That claim asks whether the relative commutant is normalized, and a positive answer to it refutes this one; the two are exact opposites and exactly one of them holds, so they are the two sides of the same fork rather than two problems.
artifacts:
  - notes/FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Find a Connes-embeddable finite tracial von Neumann algebra `M`, a
homomorphism `pi:G->U(M)` for the Kun--Thom infranormal Kazhdan pair
`Gamma<G`, and a unitary

```text
v in M intersect pi(Gamma)'   with   [v,pi(h)]!=1,
h=t^(-1) gamma t notin Gamma.
```

Equivalently (`relative-wall-commutant-growth`), make one relative commutant
grow strictly under one compressor:
`M intersect pi(Gamma)' != M intersect pi(t Gamma t^(-1))'`.

Neither faithfulness, nor the Clifford sign, nor a prescribed trace energy is
required: by `wall-energy-amplification` the energy comes for free, and by
the radical-collision endpoint the bare inequality already produces a
hyperlinear nonsofic group.  This is the weakest known sufficient hypothesis
in the whole Kun--Thom lane.

**This is packaging, not a reduction of the difficulty.**  Given a
homomorphism `phi` of the free lamp `H_K=G *_Gamma (Gamma x K)` into a
hyperlinear group with `phi(r)!=1`, put `pi=phi|_G` and `v=phi(k)`: that is a
wall.  Conversely a wall defines such a `phi`.  So this claim is *equivalent*
to the marked instance of the radical-collision criterion at `H=H_K`, and
`radical-collision-reformulation` records that the criterion is a restatement
of Question 3.4 at full strength rather than a reduction of it.  What is
gained here is only the **minimality of the data** — no faithfulness, no
Clifford sign, no trace energy, one unitary in one relative commutant — and
that is a packaging gain, not a logical one.  What keeps this claim from
being a rename of the root is that the root quantifies over all countable
groups while this one fixes the Kun--Thom pair: it is strictly stronger, so
`bare-wall-radical-collision-route` is a specialization, not an equivalence.

Its exact negation is `kt-centralizer-normalization-hs`, the tracial analogue
of Kun--Thom Theorem 4.1; establishing that would make the explicit even
Clifford cover a nonhyperlinear group.  Precisely one of the two holds, and
the fork is not symmetric in difficulty: the counting invariants that carry
the permutation proof — cell sizes and isotropy orders of an atomic partition
algebra — have no informative normalized shadow here.  By
`commutant-density-trace-blind` the only such shadow is
`lim_j sum_gamma mu_j(gamma)|chi(gamma)|^2`, which is conjugation invariant,
hence identical for `Gamma` and `t Gamma t^(-1)`, and identically zero for
every character supported at the identity.  The surviving invariant is the
Pimsner--Popa index, which `clifford-compressor-site-growth` computes to be
infinite at every strict positive compressor in the Clifford model.
