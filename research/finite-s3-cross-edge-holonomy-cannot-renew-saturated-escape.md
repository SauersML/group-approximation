---
rg: 2
id: finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape
kind: claim
title: Finite cross-edge holonomy cannot renew S3 escape beyond its prepaid type orbit
distinct_from:
  btb-three-line-tree-retains-multiplicity-return-gauge: That identifies the one genuine complete-S3 outer escape and says its orbit saturates; this treats a relation between two edge intertwiners after saturation and constructs the exact inverse-cocycle countermodel.
  agent-aggregate-escape-two-intertwiner-clifford-dichotomy: That classifies arbitrary two-intertwiner packet covariance by its twisted stabilizer algebra; this specializes the finite-holonomy branch to the two-level BTB recursion and separates full-overlap stabilizer returns from prepaid moves to new finite-orbit types.
  canonical-btb-tree-local-returns-have-stationary-reached-carrier: That treats outer-support-preserving edges starting from the protected seed; this permits the first edge to move the selected outer type and starts only after its complete S3 orbit has entered the child hull.
---

**ESTABLISHED FINITE-ORBIT FIREWALL.**  Let `P` be a fixed finite joint packet
containing the root-controlled reflection palette, and let `S` be a packet
type on which the complete irreducible `S_3` outer action gives the genuine
one-shot escape recorded in
`btb-three-line-tree-retains-multiplicity-return-gauge`.  Let `s,t` be two
edge intertwiners acting on `P` by automorphisms, and allow a finite family
of cross-edge word relations between them.

Fix the following precise class.  On the stabilizer of the `P`-type `S`,
choose outer intertwiners `C_g`.  Their multiplier is

```text
C_g C_h=omega(g,h) C_(gh).                              (FSH1)
```

Assume that the imposed cross-edge relations on the inverse multiplicity
operators factor through a finite quotient `H` of this stabilizer.  This
includes finite-order/projective holonomy, finite triangle-face two-cells,
and finite packet orbit permutations when their residual gauge relations
factor through the stated `H`.  It does not include an arbitrary finitely
presented infinite active gauge group.  Call this the **finite cross-edge
holonomy class**.

After the first complete `S_3` return, take the prescribed packet-reducing
hull.  On the active packet type it contains the complete irreducible local
`S_3` space:

```text
Q_1=1_S tensor q.                                      (FSH2)
```

Let `O` be the finite orbit of the equivalence class of `S` under the two
edge automorphisms.  Every cell in the finite cross-edge holonomy class has
an exact finite-dimensional induced realization with `q!=0` and equal
regular multiplicity on every type in `O`.

There are exactly two cases for a proposed second return word `W`.

1. If its automorphism stabilizes `S`, then `Q_1` is invariant and, for
   every `0!=F_1<=Q_1`,

```text
W F_1 W^*<=Q_1,
tau(Q_1 W F_1 W^* Q_1)=tau(F_1).                       (FSH3)
```

2. If it sends `S` to a distinct type in `O`, it may produce a further
   genuine outer-type escape, but only into one equal-size orbit summand.
   If `K subseteq O` is the set of types visited so far, the actual
   packet-reducing orbit carrier in the induced model is

```text
Q_K=direct_sum_(T in K) 1_T tensor q,
tau(Q_K)=|K| tau(Q_{ {S} }),
tau(Q_K)/tau(Q_O)=|K|/|O|.                             (FSH4)
```

Thus there are at most `|O|-1` type-moving releases, and the initial active
summand occupies exactly the reciprocal fraction `1/|O|` of the available
orbit capacity.  Cross-edge holonomy changes the multiplicity gauges but
does not alter this finite permutation ledger.

Consequently a finite projective holonomy/two-cell can couple the two edge
gauges, but it cannot produce a **non-prepaid reusable** escape.  Stabilizer
returns have full overlap by `(FSH3)`; type-moving returns merely spend the
finite capacity already present in `(FSH4)`.  This is an exact zero-defect
countermodel on the actual post-escape orbit carriers, not a proper
spectator subcarrier.

This remains a countermodel when the same cross-edge rows also admit the
required perfect marked representation with zero forbidden fiber.  Perfect
extension does not constrain the active forbidden fiber because that fiber
is absent there; the finite inverse-twisted module below realizes the rows
on a positive forbidden fiber independently.

The construction is the inverse-twisted regular model.  On `C[H]` put

```text
M_g delta_h=omega(g,h)^(-1) delta_(gh).                 (FSH5)
```

Then `C_g tensor M_g` is an honest stabilizer representation satisfying all
finite holonomy rows.  Induce it over the finite orbit of `S`.  The induced
space contains every outer orbit type with the same nonzero regular
multiplicity, and both `s` and `t` permute these summands.  A stabilizer word
preserves the current summand and proves `(FSH3)`; a nonstabilizer word moves
it to the corresponding equal summand and proves `(FSH4)`.  Tensoring with
a scalar structural assignment leaves a positive forbidden Reynolds atom,
and amplification preserves its normalized density.

Using a fresh independent `S_3` palette does not evade this theorem.
Selecting one primitive line of its two-dimensional type before use divides
the active packet capacity by two, while taking its reducing hull can release
at most that prepaid factor two.  If the fresh palette is not selected in
advance, its full local orbit is already present and the induced model routes
the return inside it.  A finite cross-holonomy relation only synchronizes the
two finite orbit sums; `(FSH5)` supplies the compatible multiplicity gauge.

The scope restriction is essential.  An infinite stabilizer quotient whose
inverse twisted group algebra has no finite-dimensional representation with
the required central character is not covered.  Its robust version is a
quantitative projective finite-dimensional radical, exactly the gate in
`agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce`.  Nor does the
claim cover a proper-corner relation which is not an automorphic packet
holonomy.  Therefore a renewing two-level cell must leave the finite
cross-edge holonomy class by supplying one of those two substantive inputs;
another finite `S_3`, Clifford, cocycle, or triangle-face coupling is fenced.

The first infinite actors beyond this scope are now fenced as well.
`minimal-s3-one-letter-actors-have-twisted-countermodels` treats the commuting
and free one-letter extensions `S_3 x Z` and `S_3 * Z`, and more generally
every virtually free active stabilizer, by retaining its finite Schur center
in a finite quotient.  It also gives twisted-regular microstate countermodels
for every amenable active stabilizer.  Thus "infinite" is not enough: the
residual twist must already be nonamenable and non-CE.

DERIVATION
finite-s3-cross-edge-holonomy-countermodel-proof
