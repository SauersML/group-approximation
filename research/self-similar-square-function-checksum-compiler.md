---
rg: 2
id: self-similar-square-function-checksum-compiler
kind: claim
title: Compile one finite relator into an orthogonal multiscale self-hash
distinct_from:
  common-source-orthogonal-partial-swap-star-compiler: that asks for two children at one scale and uses their product trace; this asks for one recursively nested carrier and one relator whose orthogonal blocks collect all scale syndromes.
  robust-locally-satisfiable-relator-code: that uses bounded-occurrence PCP checks across many sites; this asks for a single self-similar square-function word and a scalar martingale recurrence.
  finitely-presented-oligomorphic-linear-pauli-addresser: that compiles unbounded local test occurrences; this does not name occurrences and instead uses geometrically shrinking, orthogonal first-hit scale layers.
---

**OPEN.**  Construct a finite presentation `Gamma=<S|R>`, a nontrivial
involution `y`, and fixed constants

```text
0<lambda<1,       beta,C,K>0                           (SSC1)
```

with the following finite-matrix decoder.  Every sufficiently accurate
canonical-trace matrix model `U` supplies scalar carrier masses `a_n(U)` and
syndrome norms `s_n(U)` such that

```text
a_0(U)>=beta-o(1),                                    (SSC2)
a_n(U)<=lambda a_(n+1)(U)+C s_n(U)+o(1),             (SSC3)
sum_n lambda^n s_n(U)^2
 <=K sum_(r in R)||r(U)-I||_2^2+o(1).                (SSC4)
```

The `o(1)` terms must have a summable geometric envelope, so iterating
`(SSC3)` preserves a vanishing total modulus.  It is enough, and preferable,
that one fixed relator word `r_*` have orthogonal decoded first-hit blocks
`P_n` with

```text
s_n=||(r_*(U)-I)P_n||_2,                              (SSC5)
```

because Pythagoras then gives `(SSC4)` directly.

Exact completeness must give a representation with `y!=1`.  The decoded
finite scale chart is allowed to fail in that infinite representation; it
must use finite multiplicity, cyclic finite trace, or another genuinely
matrix-coordinate step.  Otherwise `(SSC2)--(SSC4)` would also kill the
marked carrier in the regular tracial representation.

The intended self-similar geometry is:

```text
root marked carrier
 -> persistent child plus first-hit exit
 -> repeat on the persistent child,
```

with the first-hit layers mutually orthogonal.  A late challenge can then be
rare, but it cannot be the only failure while the root remains macroscopic:
`(SSC3)` transports its geometric attenuation back to the root.  This is the
precise finite-presentation target left by the user's heavy-tail idea.

