---
rg: 2
id: kt-parity-fourier-orbit-and-conditional-expectation-proof
kind: route
title: Identify the cyclic parity orbit and compute its backward expectation
target: kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence
requires:
  - kt-order-three-average-does-not-kill-the-pointed-martingale-wall
  - kun-thom-single-compressor-sofic-joint-nonsofic
---

# 1. The stabilizer of the cyclic three-site set

Write the Kun--Thom actor as a semidirect product of its Laurent elementary
normal subgroup with `SL_3(Z)`. Elements of `H=B^(-1)Gamma B` have
trivial `SL_3(Z)` component. The three cosets in

~~~text
P={Gamma,C^(-1)Gamma,C^(-2)Gamma}
~~~

have actor components `1,C^(-1),C^(-2)`, respectively.

Suppose `k in H` satisfies `kP=P`. The image of the root coset
`kGamma` must belong to `P`. Its actor component is trivial, so it can
only equal `Gamma`. Thus `k in Gamma`. Conversely, every element of
`Gamma` fixes every point of `P`, because `C` normalizes
`Gamma`:

~~~text
gamma C^(-i)Gamma
 =C^(-i)(C^i gamma C^(-i))Gamma
 =C^(-i)Gamma.
~~~

Therefore

~~~text
Stab_H(P)=Gamma.                                         (1)
~~~

The inclusion `Gamma<H` has infinite index. Indeed it is conjugate to the
strict positive-compressor inclusion `B Gamma B^(-1)<Gamma`. On the
root subgroup, the latter contains only coefficients in the monomial image
ring. The distinct additive cosets represented by `x_2^n`, `n>=1`,
already show that this ring, and hence the elementary subgroup, has infinite
index.

# 2. The Fourier orbit is quasi-regular

The binary lamp group has one canonical orthonormal group basis vector
`z_F` for each finite subset `F subset G/Gamma`, with

~~~text
z_F z_L=z_(F symmetric_difference L),
tau(z_F^* z_L)=1 if F=L, and 0 otherwise.
~~~

Conjugation by an actor element sends `z_F` to `z_(gF)`. By (1), the
vectors

~~~text
v_(kGamma)=sigma(k)v sigma(k)^*=z_(kP),       k in H,
~~~

are well defined and form an orthonormal family indexed by `H/Gamma`.
Their closed span `K` is reducing for the conjugation representation of
`H`, and

~~~text
Ad(sigma(a)) v_(kGamma)=v_(akGamma).
~~~

This proves (KQR1).

Because `H/Gamma` is infinite, the quasi-regular representation has no
nonzero invariant vector: an invariant coefficient function is constant on
the transitive infinite set, and a nonzero constant is not square summable.

# 3. Exact conditional expectation

The trace-preserving conditional expectation

~~~text
E_S:L(W)->sigma(H)' intersect L(W)
~~~

is the orthogonal projection in `L^2(L(W))` onto the fixed vectors of
the conjugation representation of `H`. Since `K` is reducing and has no
fixed vector, the fixed-space projection of `v in K` is zero:

~~~text
E_S(v)=0.                                                (2)
~~~

The scalar belongs to `S`, so for `q=(1+v)/2`,

~~~text
E_S(q)=1/2.                                              (3)
~~~

Conditional expectation is the `L^2`-orthogonal projection onto `S`.
Since `v` is a trace-zero unitary,

~~~text
dist_2(q,S)
 =||q-E_S(q)||_2
 =(1/2)||v||_2
 =1/2.                                                   (4)
~~~

Equations (2)--(4) prove (KQR2).

# 4. Why this is exactly the finite-dimensional issue

For the one-compressor subgroup `<Gamma,B>`, the action on its cosets is
sofic, so finite permutation models do realize this pointed quasi-regular
orbit. The obstruction is not the correspondence (KQR1) by itself. It is
the demand that the same bounded root vector extend through the cyclic
normalizer `C` and the first Steinberg holonomy

~~~text
B_- B=D B B_-.
~~~

The full exact tracial wreath realizes that extension, but its Connes
embeddability is the target question. Therefore a tracial Fourier or
sum-of-squares argument cannot decide the route. A positive result must be a
finite-dimensional theorem about operator-norm-bounded representatives of
one named quasi-regular vector; a negative result must construct its
`C`-compatible matrix approximation.
