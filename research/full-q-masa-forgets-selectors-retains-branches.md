---
rg: 2
id: full-q-masa-forgets-selectors-retains-branches
kind: claim
title: The full q-MASA forgets the old selector subgroup but retains every corrected Schur branch
distinct_from:
  raw-schur-generator-is-not-child-center: that shows the single word q_(N+1) does not label the child types; this keeps the whole commuting q-word family, which contains every sectorwise corrected child word.
  flip-endpoints-cancel-schur-current: that treats endpoints containing the automorphism which exchanges the two child types; this endpoint deliberately omits the flip.
---

For a Schur packet `A_f<=B_f`, let

```text
K_f=<J,q_1,...,q_N,q_(N+1)> <= B_f^Q.                           (QMR1)
```

Then `K_f` is an elementary abelian two-group and

```text
K_f intersect <J,z_1,...,z_k> = <J>.                            (QMR2)
```

Nevertheless, for every selector assignment `x`, the corrected child word

```text
Q_x=q_(N+1) product_j q_j^(v_j(x))                              (QMR3)
```

belongs literally to `K_f`.  On the `x` sector it commutes with `A_f`, and
its two signs distinguish the two genuine `B_f^Q` child types whenever
`f(x)=1`.  Consequently the restrictions of those two child types to `K_f`
have disjoint character support: `Q_x` is `+1` on one support and `-1` on the
other.

Thus the complete `K_f`-character vector preserves the oriented child
branching data while no old selector generator is retained in the overlap.
The price is that the decoder is a **family** of literal words `(Q_x)_x`, not
one sectorwise-scalar word.  This is harmless for a fixed predicate because
the family is finite.

This theorem supplies a flip-free endpoint for a constant-depth reset.  It
does not by itself turn the `K_f` character multiplicities into a fresh
full-matrix packet multiplicity; that is a separate Morita incidence problem.
