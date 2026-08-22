---
rg: 2
id: arithmetic-double-swap-extension-is-binary-coset-wreath
kind: claim
title: The factor-swap extension of the arithmetic double is the binary coset wreath
distinct_from:
  sl3-arithmetic-double-embeds-in-centralizer-hnn: that embeds the double in the infinite-cyclic centralizer HNN group; this identifies the canonical order-two block swap, proves an exact equivalence of canonical microstates, and exposes the free binary coset-lamp kernel
  sl3-regular-double-bass-serre-rigidity-firewall: that exhibits the external Hilbert-space block swap in the regular group factor; this adjoins the swap as an ordinary group element while preserving the canonical microstate problem exactly
---

For any inclusion `C<=A`, put

```text
D=A *_C A
```

and let `alpha` exchange the two vertex factors.  Then

```text
E=D rtimes_alpha C_2
 ~= <A,s | s^2=1, [s,c]=1 (c in C)>
 ~= A *_C (C x C_2)
 ~= ( *_(x in A/C) C_(2,x) ) rtimes A.                 (DSW1)
```

Under this identification, the two copies of `A` in `D` are `A` and
`sAs`, and `D` is the index-two kernel of the parity homomorphism
`E->C_2` which kills `A` and sends `s` to the nontrivial element.

Canonical matrix microstates pass in both directions without loss.  Given a
canonical microstate `sigma` of `D`, define on two equal blocks

```text
tilde_sigma(d)=diag(sigma(d),sigma(alpha(d))),
tilde_sigma(s)=S=[[0,I],[I,0]].                         (DSW2)
```

The swap relations hold exactly, presentation defects are unchanged, and

```text
tr(tilde_sigma(d))
 = (tr(sigma(d))+tr(sigma(alpha(d))))/2 -> delta_e(d),
tr(tilde_sigma(sd))=0.                                  (DSW3)
```

Thus `tilde_sigma` has the canonical character of `E`.  Conversely, the
restriction of any canonical microstate of `E` to `D` is canonical.  Hence

```text
D is hyperlinear iff E is hyperlinear.                  (DSW4)
```

This is an explicit block construction, not an appeal to abstract
finite-extension permanence.

For the arithmetic pair

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),
h=diag(2,1,1/2),
```

the fold mark becomes

```text
w=i_0(h)i_1(h)^(-1)=h s h^(-1) s=[h,s].                (DSW5)
```

In every unitary representation of `E`, `tr(w)` is real, because

```text
sws=w^(-1).
```

Moreover every exact finite-dimensional representation kills `w`: the
image of `s` belongs to `rho(C)'`, finite-dimensional co-density gives
`rho(C)'=rho(A)'`, and hence `s` commutes with `rho(h)`.  In contrast the
canonical character has `delta_E(w)=0`, since `(DSW5)` is a reduced
amalgam word.

Therefore the canonical block swap removes all artificial phase freedom
from the minimal arithmetic-double mark and packages the problem as one
balanced involution in the binary coset wreath.  It does not by itself prove
collapse: `(DSW4)` shows that excluding its canonical microstates is exactly
the original non-hyperlinearity problem.
