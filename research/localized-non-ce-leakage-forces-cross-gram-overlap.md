---
rg: 2
id: localized-non-ce-leakage-forces-cross-gram-overlap
kind: claim
title: The localized non-CE moment matrix turns orthogonal exit ranges into cross-Gram overlap
distinct_from:
  corner-localized-non-ce-bcs-energy-gap: that gives a source-specific energy floor on every approximately reducing matrix corner; this applies it to exit leakage and combines it with Gram capacity.
  global-v4-exit-capacity-is-cross-gram-curvature: that proves leakage-or-overlap from dimension accounting alone; this proves that BCS-quiet leakage is impossible in matrices and hence forces the overlap alternative.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that turns a supplied cross-Gram moment into a common gauge; this supplies a positive cross-Gram lower bound from the actual shared non-CE tuple under an explicit localized covariance hypothesis.
  context-local-fanizza-exits-do-not-control-global-leakage: that proves the established occurrence bridges do not imply the localized covariance hypothesis and reduces it to one explicit capacity-gated mixed energy.
---

Fix the finite non-Connes-embeddable BCS `B`, its shared involution words
`Z=(Z_x)`, its finite residual list `R_B`, and the constant
`beta_B^corner>0` from `corner-localized-non-ce-bcs-energy-gap`.

Let `T_1,T_2` be partial isometries in a matrix algebra with source
projections `p_i=T_i^*T_i` and exit projections `E_i=T_iT_i^*`.  Let `C` be
the fixed packet capacity projection.  Assume, after fixed-packet
exactification, that `C` commutes with each `E_i`, so

```text
L_i=(1-C)E_i                                               (NCL1)
```

is the off-capacity leakage projection.  Put

```text
s=tau(p_1)+tau(p_2),
c=tau(C),
ell=tau(L_1)+tau(L_2),
Theta=||T_1^*T_2||_2^2.                                  (NCL2)
```

### The finite source-specific leakage moment matrix

For each `i`, form the Gram matrix in `L^2(M_d,tau_d)` of the finite list

```text
L_i,
Z_x L_i, L_i Z_x                    (x in X),
R(Z)L_i                             (R in R_B).             (NCL3)
```

Its entries are traces of a fixed finite list of mixed words in the original
shared BCS variables and the leakage projection.  The positive linear
functional

```text
Lambda_i
 =sum_x ||[L_i,Z_x]||_2^2
  +sum_(R in R_B)||R(Z)L_i||_2^2                         (NCL4)
```

is read directly from this Gram matrix.  Set

```text
Lambda=Lambda_1+Lambda_2.                                 (NCL5)
```

This is the first moment object in the return construction which genuinely
consumes the non-CE source rather than only the scalar forbidden mass.

### Matrix-only overlap theorem

Every finite-dimensional tuple satisfies

```text
Theta >= (s-c)/2 - Lambda/beta_B^corner.                  (NCL6)
```

In particular, whenever `s>c` and the localized leakage moment functional is
smaller than `beta_B^corner(s-c)/4`, one has the fixed positive overlap

```text
Theta >= (s-c)/4.                                         (NCL7)
```

### Proof

Apply the corner-localized non-CE gap to each `L_i`:

```text
Lambda_i >= beta_B^corner tau(L_i).
```

Therefore

```text
ell <= Lambda/beta_B^corner.                              (NCL8)
```

The two-branch Gram-capacity inequality gives

```text
2ell+2||T_1^*T_2||_2^2 >= s-c.                           (NCL9)
```

Substituting `(NCL8)` into `(NCL9)` proves `(NCL6)`.

The same argument works for the fixed finite eight-slice family: sum
`(NCL4)` over the exits and use the complete ordered cross-Gram sum in place
of `2Theta`.  Since the number of exits is fixed, a positive total overlap
selects one pair with a positive source-specific cross-Gram moment.  A
spectral cut of its Gram operator then gives the positive-density common
packet corner required by the polar-gauge route, provided the two exits
intertwine the same exactified packet.  For the three equalized eight-slice
sources, the named `S_3` reset must first identify their source packet copies;
after that identification the selected cross-Gram operator lies in the common
source commutant and its polar part is the relative gauge.

### Why this survives the regular-representation firewall

The inequality

```text
Lambda_i >= beta_B^corner tau(L_i)                        (NCL10)
```

is **not** a universal positivity consequence in finite tracial von Neumann
algebras.  It is a matrix-only compactness theorem: a sequence of matrix
corners violating it would polar-compress the shared words and create a BCS
representation in a tracial matrix ultraproduct.  In the exact non-CE
tracial model, a nonzero corner may have every residual in `(NCL4)` equal to
zero.

Thus `(NCL6)` may force overlap in matrix microstates while allowing the
regular/non-CE exact model to use the orthogonal-coordinate escape.  This is
the correct asymmetry; no cyclic SOS or finite-level NPA certificate is being
asserted.

### Source-only moments cannot force the overlap

No finite list of moments involving only the original BCS variables `Z_x`
can imply a positive lower bound on `Theta`.  Given any matrix tuple `Z`,
amplify it by a three-dimensional bookkeeping coordinate and let

```text
T_1=I tensor |1><0|,
T_2=I tensor |2><0|.                                     (NCL11)
```

Both maps intertwine every amplified source word exactly, have the same
source, and are exact isometries, while

```text
T_1^*T_2=0.                                               (NCL12)
```

Every trace moment in the `Z_x` is unchanged by the amplification.  The same
countermodel defeats any collection of branchwise moment conditions which
never contains both exits or their leakage corners.

Specifying a non-CE trace's exact finite moment profile can make the matrix
feasible set empty, but that is vacuous and does not decode a group
microstate.  A useful implication must include mixed source/exit moments.
The finite list `(NCL3)` is minimal in this structural sense: it asks whether
the leakage range approximately reduces the **same shared tuple** and whether
the BCS residuals vanish on that range.

### Claim boundary for the Fanizza compiler

The theorem proves the desired cross-Gram lower bound once the packet words
make the actual leakage projections satisfy

```text
Lambda <= K E_rel+o(1),                                  (NCL13)
```

where `E_rel` is formed from the original shared Fanizza words before the
context occurrences split.  Establishing `(NCL13)` is now the only
source-specific transport statement: the exit leakage must be an
approximately reducing, BCS-quiet corner.

This transport statement does **not** follow from the current context-local
Fanizza packet bridges.  `context-local-fanizza-exits-do-not-control-global-leakage`
gives an exact finite Bass--Serre countermodel and proves the sharp reduction

```text
Lambda <= K_B E_mix,
```

where `E_mix` consists precisely of the off-capacity blocks
`(1-C)[E_i,Z_x]` and `(1-C)R(Z)E_i`, together with commutators of `C` with the
shared tuple.  Bounding this mixed capacity-gated energy by `E_rel` is one
sufficient construction.  The weaker cancellation-friendly alternative in
`capacity-gated-common-corner-bcs-two-cell` directly controls `Lambda` by
making all allowed-context intertwiners share the analytic source `L_i`.
Contextwise survivor reduction is insufficient in either formulation.

Independent context packets do not imply `(NCL13)`, and finite tags cannot
replace it.  But if the mixed actuator relations provide `(NCL13)`, then
`(NCL6)` supplies one positive cross-Gram scalar, the polar-gauge lemma
extracts the common relative gauge on a spectral subcorner, and the two mixed
Pauli commutators lock it into the smaller reservoir.

This still does not prove the near-full overlap estimate `(SBO1)`: `(NCL6)`
gives a positive overlap forced by the capacity surplus, not overlap
arbitrarily close to the whole source mass.  It is sufficient for a fixed
holonomy floor after a controlled spectral cut, but a route which
specifically needs near-full polar alignment must add one further
amplification/return estimate.
