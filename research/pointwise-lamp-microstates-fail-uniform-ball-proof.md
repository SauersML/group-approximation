---
rg: 2
id: pointwise-lamp-microstates-fail-uniform-ball-proof
kind: route
title: Separate pointwise lamp control from uniform Ulam control
target: alekseev-thom-ulam-stability-does-not-close-the-kt-moving-window
requires:
  - finite-packet-basis-rigidifiers-leave-a-multiplicity-cocycle
  - kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence
---

# 1. The exact hypothesis in the new theorem

Alekseev--Thom, arXiv:2606.07369, Definition 2.1 and Theorem 3.5 require
one map on the whole operator-norm unit ball. In particular, the
multiplicative row is

~~~text
sup { ||phi(xy)-phi(x)phi(y)||_2 :
      ||x||<=1, ||y||<=1 } <= epsilon.                   (1)
~~~

The modulus in the conclusion is independent of `N`. Dimension freedom in
the conclusion does not remove the supremum in (1).

A hyperlinear group map has the different quantifiers

~~~text
for every fixed words a,b,
    ||phi_n(ab)-phi_n(a)phi_n(b)||_2 -> 0.                (2)
~~~

For a fixed finite lamp window, one may include its entire finite lamp group
and every pair multiplication row in the test set. Fourier linear extension
then gives control of that fixed finite-dimensional algebra, with constants
depending on the window size. This useful local rounding was already
available from finite-group Hilbert--Schmidt stability. It does not turn (2)
into (1) for the infinite lamp algebra.

# 2. An exact quantifier counterexample inside R

Let

~~~text
R=tensor_(j=1)^infinity M_2(C),
A_n=tensor_(j=1)^n M_2(C),
E_n:R->A_n
~~~

be the standard increasing matrix subfactors and their trace-preserving
conditional expectations.

For fixed `x,y in R` and `epsilon>0`, choose `m` and
`x_0,y_0 in A_m` with

~~~text
||x-x_0||_2<epsilon,       ||y-y_0||_2<epsilon,
||x_0||<=||x||,            ||y_0||<=||y||.
~~~

For `n>=m`, `E_n(x_0)=x_0`, `E_n(y_0)=y_0`, and
`E_n(x_0y_0)=x_0y_0`. Conditional expectations are contractions in
operator norm and in `L^2`. Expanding around `x_0,y_0` therefore gives

~~~text
||E_n(xy)-E_n(x)E_n(y)||_2 <=4 epsilon
~~~

when `x,y` are contractions. This proves (KUS1).

On the other hand, let `z` be a trace-zero self-adjoint unitary in the
`(n+1)`-st tensor factor. Then

~~~text
E_n(z)=0,             E_n(z^2)=E_n(1)=1.
~~~

Hence

~~~text
||E_n(z^2)-E_n(z)^2||_2=1.                               (3)
~~~

The defect is never larger than one for these unital completely positive
maps. Indeed, using the `A_n`-bimodule property,

~~~text
E_n(xy)-E_n(x)E_n(y)=E_n((x-E_n(x))y).
~~~

For contractions, `L^2` contractivity and the orthogonal-projection
identity give

~~~text
||E_n((x-E_n(x))y)||_2
 <=||x-E_n(x)||_2
 <=||x||_2
 <=1.
~~~

Together with (3) this proves (KUS2).

The gap survives exact pointwise actor covariance. Use the bilateral tensor
product `R=tensor_(j in Z)M_2`, the shift automorphism `alpha`, the
windows `A_n=tensor_(-n<=j<=n)M_2`, and their expectations `E_n`.
For every fixed `x in R` and fixed integer `k`,

~~~text
||E_n(alpha^k(x))-alpha^k(E_n(x))||_2 ->0,               (4)
~~~

because both terms converge to `alpha^k(x)` in `L^2`. Yet the same
next-site unitary proves that the supremum in (1) is one for every `n`.
Thus even pointwise covariance under a genuine actor does not reverse the
quantifiers.

# 3. What finite-factor rounding leaves behind

Suppose, more strongly than the binary KT data provide, that a full matrix
packet has been rounded to an exact unital embedding

~~~text
theta:M_N(C)->P.
~~~

Let `U` normalize `theta(M_N)` and induce the automorphism `alpha`.
Every automorphism of `M_N` is inner, so choose `w in U(N)` with

~~~text
alpha(a)=w a w^*.
~~~

Then

~~~text
V=theta(w)^* U
~~~

commutes with `theta(M_N)`, and therefore

~~~text
U=theta(w)V,       V in theta(M_N)'.                     (5)
~~~

Conversely every such `V` gives the same action on the rounded factor.
Thus even perfect, uniform lamp-algebra rounding cannot see the
multiplicity unitary.

For several actor generators, their products impose a cocycle equation on
the corresponding `V_g`'s. Property (T) may give spectral information
about that cocycle, but no estimate on it is supplied by the lamp
homomorphism or by Theorem 3.5. Controlling one pointed `V_g` is exactly
the bare multiplicity problem isolated by the regular trace mask.

# 4. The binary and Pauli conclusions

For binary lamps, the theorem cannot create missing matrix units. Rounding
`C^(2^m)` produces an exact atomic algebra with arbitrary atom
multiplicities and block-unitary normalizers.

For a Pauli enrichment, the finite window is a full matrix factor and
Theorem 3.5 genuinely applies if (1) is available. Equation (5) then shows
that it stops at the same arbitrary multiplicity algebra. Passing to the
small amplification allowed by the theorem changes neither conclusion.

Finally, the named parity and its `h`-translate already lie in a fixed
finite lamp packet. Exactifying that packet preserves their trace
orthogonality and the Fourier distance

~~~text
dist_2(q,Phi_B(R))=1/2.
~~~

The missing step is actor/multiplicity exactification, not lamp-algebra
Ulam stability.
