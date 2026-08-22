---
rg: 2
id: bounded-radial-simplex-templates-have-vanishing-linearized-gap
kind: claim
title: Bounded radial simplex templates have a vanishing linearized cyclic gap
distinct_from:
  radial-only-group-needs-a-cyclic-gcd-audit: that decides whether the exact scalar kernel has only the affine modes; this proves that even a correct exact kernel has no uniform linearized inverse
  radial-parallelograms-kill-simplex-class-two: that gives a uniform exterior-square detection and class-two rounding estimate; this concerns scalar coordinate/agreement modes before the class-two obstruction
  affine-simplex-riesz-inverse-is-uniformly-cb: that uses the dense complete-pair table and the two-weight spectrum; this proves a bounded family of radial shifts cannot inherit that cb inverse
---

Index the nonzero points of `F_(2^n)` by the cyclic group `Z/m`,
`m=2^n-1`.  Consider any radial occurrence presentation obtained from at
most `D` shift offsets (a fixed number independent of `n`), with every local
linearized scalar relation a translate of one of finitely many bounded masks
supported on those offsets.  Assume the constant mode is accepted, so every
mask polynomial `p_r` satisfies `p_r(1)=0`.

Even if the cyclic gcd audit proves that the exact common kernel is precisely
the `n+1` affine/simplex Fourier modes, the normalized linearized soundness
gap tends to zero.  More precisely, there is a Fourier character outside
that exact kernel, at `L_2`-distance one from it, whose total normalized
residual energy is

```text
 O_D(((2n+3)/m)^(2/D)).                                  (BRG1)
```

To see this, write the offsets as `s_1,...,s_D in Z/m`.  Partition the
`m` points

```text
 (k s_1/m,...,k s_D/m) mod 1,   k in Z/m,
```

into at most `m/(2n+3)` equal cubes (rounding the number of cubes changes only
the constant).  One cube contains at least `2n+3` points.  Taking differences
from one of them gives at least `2n+2` distinct nonzero frequencies `k` with

```text
 max_j ||k s_j/m||_(R/Z)
    <= O_D(((2n+3)/m)^(1/D)).                            (BRG2)
```

At most `2n` frequencies belong to the complex affine kernel or its
conjugate (negative-frequency) set, so one of these frequencies and its
conjugate both lie outside it.  Since every bounded mask vanishes at
one, telescoping gives

```text
 |p_r(exp(2 pi i k/m))|
   <= C_r max_j |exp(2 pi i k s_j/m)-1|,                (BRG3)
```

and `(BRG1)` follows.  Taking real and imaginary parts gives the same
obstruction in a real/self-adjoint tangent space.

Thus the finite cyclic gcd condition is only an exactness check.  A bounded
number of radial parallelogram orbits cannot provide the dimension-free
coordinate cb inverse or operator-norm Newton tube needed by an off-exact
simplex decoder.  Radial checks may still be retained for their uniform
exterior-square/class-two gap, but a non-cyclic agreement mechanism must
supply coordinate soundness.

This is a linearized/cb no-go, not a refutation of every nonlinear HS modulus:
quadratic curvature can turn a small tangent eigenvalue into a weaker
square-root-type correction law.
