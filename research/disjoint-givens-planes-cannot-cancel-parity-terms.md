---
rg: 2
id: disjoint-givens-planes-cannot-cancel-parity-terms
kind: claim
title: Orthogonal Givens escape planes cannot cancel recurrent terms in a constant-parity context
distinct_from:
  rstar-hadamard-escape-violates-term-c4: that treats one rank-two plane and derives a two-piece relator; this proves that taking any finite direct sum of such planes cannot create coefficient cancellation.
  edgeful-one-ghost-escape-avoids-term-recurrence: that changes the source relation so a single plane has Hamming support one; this keeps the constant-parity source and audits multi-plane cancellation.
---

Let a context relation `R subseteq F_2^m` lie in one parity coset.  Refine its
assignment atoms into coordinate copies and let `U` be a direct sum of
nontrivial `2 by 2` real rotations on pairwise disjoint coordinate planes.
Assume every plane joins copies of two distinct assignments and give every
coordinate an independent free phase, as in the standard signed-Hecke
escape.

For a plane `(r,s)` labelled by assignments `a!=b`, the coefficient of
`h_r h_s^(-1)E_rs` in marginal `X_y` is

```text
c_(rs) ((-1)^(a_y)-(-1)^(b_y)),                        (DGP1)
```

where `c_(rs)` is the nonzero sine-cosine product of that plane.  Since
`a,b` have the same total parity, their positive Hamming distance is even
and hence at least two.  The full term in `(DGP1)` therefore occurs in at
least two logical marginals.

Terms from different planes cannot cancel it.  They occupy different matrix
units `E_pq`; after the free-phase conjugation they additionally carry
different reduced words `h_p h_q^(-1)`.  Linear independence of the packet
matrix units (or, after expanding them in the finite group, uniqueness of
the matrix coefficient before expansion) makes cancellation across planes
impossible.  Thus every nontrivial plane retains its own repeated full term,
no matter how many disjoint planes are added.

Consequently a multi-plane repair of the R-star termwise `C(4)` obstruction
must use genuinely overlapping rotations or deliberately identify phase and
root support terms so that several assignment contributions meet in the
same matrix coefficient.  A direct sum of private Hadamard/Givens cells is
not such a repair.  The claim makes no assertion about an overlapping dense
unitary, where the sums over several assignments can cancel.
