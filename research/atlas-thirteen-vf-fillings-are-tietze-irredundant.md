---
rg: 2
id: atlas-thirteen-vf-fillings-are-tietze-irredundant
kind: claim
title: The thirteen virtually-free Atlas fillings are Tietze-irredundant
distinct_from:
  atlas-augmented-thirteen-vf-fillings: that constructs the virtually free carrier and counts its graph cycles; this fixes a maximal tree, eliminates every bridge generator, and proves that no displayed filling is a consequence of the others.
  atlas-a4-packet-four-rectangle-normal-form: four rectangle holonomies control analytic edge-message factorization after gauge; they are not dependencies among the twelve abstract cross-chart pair-cube relators.
---

In the graph of finite groups from `atlas-augmented-thirteen-vf-fillings`,
choose the following maximal tree:

1. include both edges incident to the q14 bridge `L_14 ~= V4`;
2. for each of the twelve packet bridges `L_e ~= A4`, include its `C3` edge
   and omit its `C2` edge.

This has fourteen edges on fifteen vertices.  Let `G_T` be its tree
amalgam.  If `a_e,b_e` are the order-three and order-two generators of
`L_e`, let `bar_b_e` be the marked chart involution at its omitted endpoint.
Then the virtually free carrier has the explicit HNN presentation

```text
Pi=<G_T,s_1,...,s_12 |
       s_e^-1 b_e s_e=bar_b_e  (1<=e<=12)>.           (TIR1)
```

Filling `s_e=1` identifies `b_e=bar_b_e`.  Since the tree edge has already
identified `a_e` with its marked order-three chart element, eliminating the
two bridge letters converts the `A4` law `(b_e a_e)^3=1` into exactly the
original cross-chart packet relation.  Therefore

```text
Gamma_+ ~= G_T/<<
  (bar_b_e a_e)^3  (1<=e<=12), q_19243>>.             (TIR2)
```

After eliminating all finite bridge vertices as well, this is the literal
relative presentation over `A8*A8`

```text
<A8,A8 |
  twelve distinct packet pair-cubes,
  [t23_1,t23_2],
  q_19243>.                                           (TIR3)
```

The q14 commutator is already the relation carried by the central `V4` tree
bridge; it has not disappeared or been inferred from the packet.

The thirteen relators in `(TIR2)` are irredundant.  Killing every vertex
group gives the canonical epimorphism

```text
Pi -> pi_1(|G|) ~= F_12,
```

under which the stable letters are a free basis and collision maps to one.
Thus no stable-letter filling belongs to the normal closure of the other
eleven together with collision.  Conversely, after all twelve stable letters
are filled, identify the two marked charts by the identity automorphism of
`A8`.  Every packet pair-cube and q14 holds, while collision is nonidentity
by the exact classical-alignment audit.  Hence collision is not in the normal
closure of the twelve stable fillings.

Thus the post-elimination compatibility rank is exactly twelve and collision
adds one independent relator: the displayed relative filling set has
irredundancy rank thirteen.  This does not assert an unrelated global
Andrews--Curtis minimum over arbitrary changes of generators; it proves that
symbolic elimination of the graph stable letters cannot reduce the augmented
quotient to a tree amalgam with collision as its only remaining relation.
