# Odd corner relations of lengths five and seven

## Result

There are no cyclically reduced coefficient relations of length five or
seven in the six corner labels of the three-gate Leavitt candidate.

The exact counts modulo cyclic rotation and inversion are

```text
length 5:  1682 representatives
length 7: 58826 representatives.
```

Every representative is nontrivial in `G_0*G_1`.

## Symbolic reduction

Only the bridge labels cross free factors:

```text
h_1=q_0p_1,       k_2=p_0e_1.
```

After expansion, adjacent atoms in the same copy are collected.  The root
packets `a,e,q` are commuting involutions: `a,e` lie in the same root
subgroup, and both root supports of `q` are disjoint.  Root-only syllables
therefore reduce exactly by parity in the elementary abelian group
`<a,e,q>`, while adjacent `p,p^(-1)` cancel.  Deleting a trivial syllable may
join its two neighbors, so the simplification is iterated to closure.

The only blocks not immediately separated by a moved-vector witness before
this simplification were

```text
(ae)^2, (aq)^2, (qa)^2,
e(aq)^2e, p(aq)^2p^(-1), q(ae)^2q, e(qa)^2e.
```

Each is exactly the identity by the commuting-root relations.  Once these
blocks are deleted, the neighboring free-factor blocks merge.  Every merged
block has an explicit moved vector in the standard infinite-word module.
The final audit has zero survivors in both lengths.

## Picture consequence

An eight-cell picture with at least two odd internal faces would have one of
length five or seven by the 24-corner curvature count.  This theorem excludes
that entire branch.  A remaining eight-cell picture must have exactly one
odd internal face, paired in parity with the outer face, and its internal
length must be `9,11,13`, or `15`.

The computation was run on MSI.  It is finite and exact: moved vectors are
one-sided certificates of nonidentity, and every block without such a
certificate is reduced symbolically by the displayed root relations before
the free-product normal-form test.
