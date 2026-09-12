---
rg: 2
id: edgeful-or3-four-cap-walsh-packet
kind: claim
title: Four affine OR3 caps give a balanced Fourier packet with zero root diagonal
distinct_from:
  edgeful-or3-balanced-private-plane-packet: that ten-coordinate packet has one private Hamming-edge plane per literal and a nonzero root-diagonal skeleton; this sixteen-coordinate packet kills every root diagonal but has three precisely classified capwise matching repetitions.
  finite-lcs-product-sign-is-exact-or: that combines already constructed marked LCS branches by central selectors; this is only a local finite-packet decomposition of the OR3 assignment PVM and does not establish compatible central cap selectors across contexts.
---

**ESTABLISHED.**  Write the seven satisfying assignments of OR3 as
`G\{0}`, where `G=F_2^3` has coordinates `a,b,c`.  For

```text
L={110,101,011,111},
H_l={x in G : l dot x=1},                               (OCW1)
```

take one four-dimensional block for every affine cap `H_l`.  The resulting
assignment multiplicity is

```text
n(100)=n(010)=n(001)=3,
n(110)=n(101)=n(011)=2,
n(111)=1.                                               (OCW2)
```

Thus every honest OR3 atom is nonzero, the total dimension is `16`, and each
logical marginal has ranks `8+8`.

On the `l` block choose `t_l in H_l`, put `V_l=ker(l)`, identify
`H_l=t_l+V_l`, and apply the Walsh transform

```text
F_l delta_u = (1/2) sum_(chi in V_l^*) (-1)^(chi(u)) delta_chi.
```

If `D_j` is the diagonal sign for logical coordinate `j`, then

```text
F_l D_j F_l^* = (-1)^((t_l)_j) T_(e_j|V_l),             (OCW3)
```

where `T_phi delta_chi=delta_(chi+phi)`.  None of the four `l` is a
coordinate vector, so every `e_j|V_l` is nonzero.  Hence every operator in
`(OCW3)` is a fixed-point-free signed permutation: two disjoint
transpositions and **no diagonal coefficient**.  The direct-sum packet
therefore removes the root-diagonal slot-matching problem simultaneously for
all three logical marginals.  This has an explicit finite group-algebra
host.  If `E` is the two-qubit extraspecial Pauli group, `p_-` is its
nontrivial central-character projection, and `A=C_2^2`, then

```text
q C[E times A] q = M_4(C) tensor C[A]
                  = direct_sum_(l in L) M_4(C),
q=p_- tensor 1.                                           (OCW3a)
```

Label the four character blocks of `A` by `L`.  The Walsh matrices and all
assignment idempotents lie in this corner.  Thus the packet has a finite
group-algebra realization; all assignment projections remain exact and
their sum is `q`.

The repeated matchings are exactly the affine parity identities:

```text
l=110:  S_a=-S_b,
l=101:  S_a=-S_c,
l=011:  S_b=-S_c,                                      (OCW4)
l=111:  the a,b,c matchings are the three distinct
        perfect matchings of the four block coordinates.              (OCW5)
```

There are no other repeated capwise matchings.  Diagonal free-phase
wordization preserves `(OCW4)` exactly.  Indeed, for
`W_l=sum_chi h_(l,chi) E_(chi,chi)`, one oriented matching has the explicit
coefficient expansion

```text
W_l T_phi W_l^*
 =sum_(chi in V_l^*)
   h_(l,chi+phi) h_(l,chi)^(-1) E_(chi+phi,chi).         (OCW7)
```

Thus equality of the translations in `(OCW4)` is equality of the full
endpoint phase words and matrix units, not merely equality of their
unlabelled support graphs.

Only adjoint duplication may be omitted automatically from a coefficient
presentation.  For one self-adjoint marginal, the equation on the reverse
matrix unit is the adjoint/inverse of the chosen equation.  By contrast, the
same local matching occurring in two different marginals in `(OCW4)` is not
redundant: if those marginals represent different global variables, the
first overlap equality does not imply the second unless the corresponding
global target coefficients already satisfy the same signed cap relation.
Thus the packet proves zero root diagonal and classifies all recurrence, but
does not by itself supply compatible cap selectors across clauses.
