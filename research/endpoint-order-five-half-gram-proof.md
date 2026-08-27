---
rg: 2
id: endpoint-order-five-half-gram-proof
kind: route
title: Compute the GL4 endpoint actor, its half Gram, and the signed-sheet exits
target: endpoint-order-five-actor-has-half-gram
requires:
  - endpoint-whitehead-hecke-flag-trichotomy
  - native-whitehead-hecke-head-has-order-seven-anchor
  - endpoint-detector-cell-retains-coboundary-gauge
---

Prefix cancellation and ordinary non-opposite Steinberg collection give
the images in `(OFG4)`.  In the ordered exponent basis
`(C_3,s,t,s')`, they are the two matrices whose columns are

```text
M=(1+4, 4, 1+2, 8),              W=(1, 8, 4, 2)       (1)
```

in four-bit notation.  Exact multiplication gives orders `7,2,5` for
`M,W,WM`.  Breadth-first closure of these sixteen-bit matrices has order
`20160`, and the orbit of any nonzero vector has size `15`.  Since

```text
|GL_4(F_2)|=(16-1)(16-2)(16-4)(16-8)=20160,
```

this proves `(OFG6)` and transitivity without identifying the actor by an
order coincidence alone.

There is also a direct global block proof.  Prefix cancellation shows that
the projection `D` in `(OFG5)` reduces both words.  The native three-corner
calculation identifies `M|D` with its faithful Singer matrix on the first
three summands and the identity on the fourth.  The endpoint Whitehead is
the swap of summands two and four.  These are exactly the four-bit matrices
in `(1)`, tensored with the common projective reservoir, and both are the
identity off `D`.  Hence the finite actor is a literal subgroup of the
elementary group, not merely a quotient of its action on four named roots.

For any representation, restrict to `V` and decompose into its sixteen
joint characters.  Conjugation by `GL_4(F_2)` preserves multiplicities and
has precisely the zero orbit and the nonzero orbit.  The equations

```text
C_3=-1, s=+1
```

select `2^2=4` nonzero characters; adding `s'=+1` selects `2`.  This proves
`(OFG8)`.  Conjugating the first projection by `W` replaces the `s=+1`
condition by `s'=+1`, so multiplication of the commuting spectral
projections proves `(OFG9)`.

For the signed sheet, the vector-and-covector stabilizer of the first basis
vector in `GL_4(F_2)` is exactly `diag(1,GL_3(F_2))`, proving `(OFG10)`.
The support incidences listed in the claim show directly that it fixes all
five generators of `K_1`; no long-word conjugation audit is needed.  The
roots `s,t,s'` commute with `K_1`, so their spectral projections reduce
`p_1`.  Character covariance under the returned `GL_3(F_2)` gives the two
multiplicities `m_0,m_1`.  The full character space contains zero and seven
nonzero characters, a hyperplane contains zero and three nonzero characters,
and the intersection of two independent hyperplanes contains zero and one
nonzero character.  This proves `(OFG11)--(OFG12)`.

The same exact sparse collection gives `(OFG13)`.

All matrix and finite-actor assertions are reproduced by
`experiments/endpoint_fine_collision_odd_mixed_audit.py`.  Its native
orientation is `J_2=What_(8,9;2)`.  A second faithful sparse Leavitt replay
checks `M^7=(WM)^5=1` without bounding prefix length; this prevents the
four-bit root action from being misread as a finite-prefix quotient.  The
script runs only through MSI and its exact four-bit closure finishes in
under four seconds.  No numerical tolerance or random search occurs.
