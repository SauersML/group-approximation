---
rg: 2
id: boone-base-semidirect-product-is-hnn-over-free-subgroups
kind: claim
title: With one state marker the Boone base semidirect product is a central HNN of one HNN over free subgroups of a symmetric amalgam
distinct_from:
  boone-instruction-twists-extend-to-base-automorphisms: that produces the semidirect product `B x| F_I` as the envelope; this decomposes the envelope into pieces whose MF status is known except for one edge.
  boone-base-has-corona-inner-instruction-automorphisms: that is the open corona statement; this converts it into a single explicit HNN edge over free subgroups.
---

ESTABLISHED.  Encode the Turing machine by a special semigroup in which every
non-terminal relation `F_i q_1 G_i = H_i q_1 K_i` uses one state marker
`q_1` (the state is stored in the tape letter adjacent to the marker; the
terminal marker `q_0` is untouched by the relations).  Then the Boone base is
`B = G_1 * F(q_0, q_1)`, the instruction automorphisms are `Theta_i = psi *
(q_1 -> u_i q_1 v_i, q_0 -> q_0)` with `u_i, v_i in G_1`, and

```text
B x| F_I = < H_1, q_1, q_0 |
             q_1^-1 (u_i^-1 theta_i) q_1 = v_i theta_i (i in I),
             [q_0, theta_i] = 1 (i in I) >,                           (BS1)
H_1 = G_1 x| F_I = *_(G_1) (G_1 x|_psi <theta_i>)_(i in I).           (BS2)
```

So `B x| F_I` is a central HNN extension (letter `q_0`) of the HNN extension
of `H_1` by `q_1` between the free subgroups `F_a = < u_i^-1 theta_i >` and
`F_b = < v_i theta_i >`, basis to basis.  `H_1` is a symmetric amalgam over
`G_1` of copies of the regularly MF group `G_1 x|_psi Z` of
[[rotman-g1-is-central-hnn-of-baumslag-solitar]], hence `C*(H_1)` is MF
(Shulman, Lemma 17).  Consequently

```text
C*(B x| F_I) is MF   <==   the q_1 edge of (BS1) is MF-safe,           (BS3)
```

and by [[boone-instruction-twists-extend-to-base-automorphisms]] this makes
the Boone group MF.

## Proof

`theta_i q_1 theta_i^-1 = u_i q_1 v_i` is `q_1^-1 (u_i^-1 theta_i) q_1 = v_i
theta_i`, and `theta_i q_0 theta_i^-1 = q_0` is `[q_0, theta_i] = 1`; the
`theta_i` act on `G_1` by `psi`, which is `(BS2)` by Shulman's Proposition
28 (a semidirect product by a free group is the amalgam over the base of the
mapping tori).  The retraction `H_1 -> F_I` killing `G_1` carries both
`{u_i^-1 theta_i}` and `{v_i theta_i}` to the free basis `{theta_i}`, so
both families are free bases of free subgroups and `q_1` is an HNN letter.
`q_0` centralizes `<theta_i> = F_I <= H_1`, a central HNN move.

## The remaining edge

Both edge tuples `(Phi(u_i^-1 theta_i))_i` and `(Phi(v_i theta_i))_i` have
the free-Haar `*`-distribution with respect to the regular character of
`H_1`, so no tracial invariant separates them; what is needed is a corona
unitary conjugating one tuple to the other.  For `|I| = 1` this is a
spectral statement (two infinite-order elements with Haar spectral
distribution are conjugate in the corona); for `|I| >= 2` it is a genuine
free-group conjugacy question in the corona, and Hadwin's rank
characterization of approximate equivalence is the natural tool.  Note the
edge cannot be split into cyclic edges: one letter `q_1` must carry all
instructions at once, because the same state marker occurs in every
relation.
