---
rg: 2
id: relation-cocycle-rectangle-proof
kind: route
title: Localize a normalized relation cocycle on transformation supports
target: relation-cocycles-preserve-full-group-rectangles
requires: []
---

Use the convention

```text
(u_g f u_g^*)(x)=f(g^(-1)x).
```

For `a_g` from `(RCR1)`, the cocycle identity gives, almost everywhere,

```text
a_g(x) a_h(g^(-1)x)
 =c(x,g^(-1)x)c(g^(-1)x,h^(-1)g^(-1)x)
 =c(x,h^(-1)g^(-1)x)
 =a_(gh)(x).                                            (RCP1)
```

Therefore `w_gw_h=w_(gh)`, while normalization gives `w_1=1`.  Thus the
displayed family is a unitary representation.

The Cartan expectation of a full-group Fourier term is

```text
E_(A tensor M_n)(a_g(u_g tensor 1_n))
 =1_(Fix(g)) a_g.                                      (RCP2)
```

On `Fix(g)` the relation arrow `(x,g^(-1)x)` is the identity arrow
`(x,x)`, so `a_g(x)=c(x,x)=1_n`.  Applying the normalized matrix trace to
`(RCP2)` proves `(RCR2)`.

Put `p_g=1_(supp(g)) tensor 1_n`.  The support of a transformation is
`g`-invariant.  On its complement, `g` is the identity and normalization
again gives `a_g=1_n`.  Consequently

```text
w_g-1=p_g(w_g-1)=(w_g-1)p_g.                           (RCP3)
```

If `supp(g)` and `supp(h)` are disjoint, then `p_gp_h=0`; multiplying the
two identities `(RCP3)` proves

```text
(w_g-1)(w_h-1)=0.                                      (RCP4)
```

Expanding `(RCP4)` and using `(RCP1)` gives `(RCR3)`.  Nontrivial
transformations with disjoint supports cannot equal one another, and their
product cannot be `1`, `g`, or `h`; hence `1,g,h,gh` are distinct.  Thus

```text
gh-g-h+1
```

is a nonzero element of `C[Lambda]` killed by the representation.  In the
left regular representation its four terms are orthonormal and its squared
`L^2` norm is `4`, which independently certifies that the group-ring element
is nonzero.

Finally let `v_k=z_k w_k`, where `z_k in T` and `z_1=1`.  Substitution in
`(RCR3)` gives `(RCR4)`, whose four coefficients are nonzero.  Moreover

```text
v_gv_h=(z_g z_h z_(gh)^(-1))v_(gh),                   (RCP5)
```

so this is indeed a projective representation, with a scalar coboundary
multiplier.  The rephased vectors are linearly dependent and cannot be an
orthonormal projective group basis.  Also

```text
abs(tau_n(v_g))=mu(Fix(g)),                             (RCP6)
```

so rephasing cannot turn a positive fixed-point coefficient into the
regular trace.

The distinction at the theorem's boundary is literal.  If
`b in Z^1(Lambda,U(A tensor M_n))` is a cocycle for the transformation
action and `V_g=b_g(u_g tensor 1_n)`, then

```text
tau_n(V_g)=integral_(Fix(g)) tr_n(b_g(x)) dmu(x).       (RCP7)
```

The transformation groupoid retains the isotropy arrow `(g,x)` when
`gx=x`; its cocycle may assign that arrow a nonidentity unitary.  Pullback
from the principal relation replaces `(g,x)` by the identity arrow and
forces `b_g(x)=1_n` there, which is exactly the step used in `(RCP2)` and
`(RCP3)`.  Hence arbitrary isotropy-sensitive transformation cocycles remain
outside the claim.

For comparison, the scalar untwisted relation `(RCR3)` appears for
topological full groups in Alekseev--Finn-Sell, *Representation theory of
topological full groups of etale groupoids and paradoxicality*, Semigroup
Forum 110 (2025), Lemma 5.3.  The proof above is self-contained and adds the
normalized finite-rank local-system, trace, and projective-rephasing
statements.
