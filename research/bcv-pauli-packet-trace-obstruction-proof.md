---
rg: 2
id: bcv-pauli-packet-trace-obstruction-proof
kind: route
title: Compute the forced packet trace and isolate the missing crossed-product data
target: bcv-pauli-amplification-haarizes-only-the-packet
requires:
  - bcv-every-perfect-question-reduction-amplifies-readable-closure
  - bcv-every-perfect-compression-amplifies-readable-closure
---

Put `A=F_2^k`. The monomial normal form supplied by the first
prerequisite is

```text
H=ell^2(A) tensor K.
```

Normalized matrix trace therefore factors as `tr_A tensor tau_K). In the
standard packet basis,

```text
<z|X^a Z^c|z> = 1_(a=0) (-1)^(c dot z).
```

Summing over `z` and using character orthogonality gives

```text
tau((X^a Z^c) tensor b)
  =delta_(a,0) delta_(c,0) tau_K(b).
```

This proves `(PHT1)--(PHT3)`. If
`C=sum_z e_z tensor C_z`, then `X^a e_z X^(-a)=e_(z+a)`;
multiplying diagonal blocks and taking their normalized trace gives
`(PHT5)--(PHT7)`.

BCV equation `(45)` identifies this irreducible packet with the
`J=-1` central corner of the finite Pauli group algebra. Its normalized
trace is the matrix trace just computed. But the represented central
involution is `J=-I`, so its trace is `-1`; the canonical group trace
of the nonidentity element `J` is zero. Hence packet Haar trace is not
the ordinary Pauli group trace.

For the source-fiber obstruction, take the one-question game with
`ell_R=ell_L=1`, force the readable bit to zero, and impose synchronous
equality on the unreadable bit. Given any diagonal signed involution `U`,
use the two projections `(I+U)/2,(I-U)/2` at both ends of the sole loop.
This is a perfect signed-permutation ZPC strategy. With

```text
U=diag(1,1,-1)
```

the unreadable generator has normalized trace `1/3`, although it
represents the nonidentity element of `C_2`. Question Reduction adds the
same packet to this strategy without changing that tail moment, proving
that perfectness cannot force the whole character to be canonical.

For any finite recursive chain, apply the second prerequisite successively
and compose its monomial unitaries. Ordinary associativity of finite tensor
products gives `(PHT8)`, and trace factorization gives `(PHT9)`.
This construction chooses a new restricted/coarse-grained strategy and a
new monomial identification at each level. Existence of those finite
factorizations supplies no compatible inclusions, endomorphism, or
normalizing shift unitary. Thus the syntactic fixed point cannot imply a
crossed product.

The packet `X)-action also cannot serve as a lamp-site shift. On
`D=L(F_2^k)`, equation `(PHT10)` translates the spectrum. A nonzero
translation moves the trivial character, whereas the dual of a group
automorphism fixes it. The resulting finite crossed product is the full
matrix algebra of the translation pair-groupoid, the same negative Pauli
corner, not a lamplighter semidirect product.

Finally, assume the three extra hypotheses stated before `(PHT11)`.
For an algebraic crossed-product element `x=sum_g d_g v_g`, covariance
and the conditional-expectation condition give

```text
||x||_2^2 = sum_g ||d_g||_2^2.
```

Indeed, every `g!=h` cross term has a factor `v_(g^(-1)h)` and zero
conditional expectation, while the diagonal terms are the displayed
squares. Hence the integrated covariant representation preserves the
faithful canonical trace and is `L^2)-isometric. It extends normally and
injectively to the von Neumann crossed product, and its image is exactly
`W^*(D,{v_g})`. This proves `(PHT12)` and shows that coherent action
unitaries plus Fourier vanishing are precisely the additional data absent
from the BCV packet equations.
