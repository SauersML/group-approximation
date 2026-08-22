---
rg: 2
id: affine-frobenius-group-has-almost-full-simple-block
kind: claim
title: The affine Frobenius group has one simple block of canonical mass one minus one over p
distinct_from:
  finite-torus-root-fourier-has-stationary-aliases: that audits conjugation-weight components in an affine root packet and proves they do not linearize coefficients; this identifies the complementary primitive central block and its full matrix algebra.
  standard-type-thin-common-reflection-sector: that obtains a high relative accepting mass inside a low-Plancherel symmetric-group type; this gives a primitive block whose absolute canonical Plancherel mass tends to one.
  every-boolean-predicate-has-a-character-free-finite-type-block: that constructs predicate-specific finite types; this supplies one universal full matrix block with arbitrarily high canonical mass.
---

Let `p` be an odd prime and

```text
H_p=F_p rtimes F_p^x,
N=(F_p,+) triangleleft H_p,
e_N=(1/p)sum_(t in N)t,
q_p=1-e_N.                                             (AFB1)
```

Then `q_p` is a central projection and

```text
tau_(H_p)(q_p)=1-1/p.                                  (AFB2)
```

It is the primitive central projection of the unique nonlinear irreducible
representation of `H_p`, whose dimension is `p-1`.  Consequently

```text
q_p C[H_p] q_p isomorphic M_(p-1)(C).                  (AFB3)
```

Thus arbitrary matrix data of size at most `p-1` can be stored in one simple
finite group-algebra block whose **absolute canonical** mass tends to one.

