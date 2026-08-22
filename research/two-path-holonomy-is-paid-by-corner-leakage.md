---
rg: 2
id: two-path-holonomy-is-paid-by-corner-leakage
kind: claim
title: Two-path relative holonomy is paid exactly by corner leakage
distinct_from:
  d8-two-path-corner-cell-is-a-gauge-free-swap: that computes one isolated swap, whose only path gauge is removable; this treats two coherent paths with the same source and range and computes their gauge-invariant relative holonomy.
  transverse-d8-two-swap-corner-unitarity-collapses-to-one-path: that studies one particular transverse Pauli product and forces exact corner unitarity; this gives the packet-independent positive-Gram identity, its robust HS bound, and the exact global-unitary dilation escape.
  fixed-packet-julia-calculus-is-tracially-functorial: that is a general regular-firewall theorem for continuous packet calculus; this identifies the precise Julia defect of a two-path arithmetic coefficient and the additional invariant-corner hypothesis that removes it.
---

# Two-path relative holonomy is paid exactly by corner leakage

ESTABLISHED.  Let `(M,tau)` be a finite tracial algebra and let `p,q` be
projections of the same positive trace.  Suppose `A,B in pMq` are two
unitary transports with the same source and range:

```text
A^*A=B^*B=q,          AA^*=BB^*=p.                       (TPH1)
```

Their gauge-invariant cross term and normalized two-path average are

```text
V=A^*B in qMq,         K=(A+B)/2=A(q+V)/2.               (TPH2)
```

Changing source and range frames conjugates `V` by the source gauge, so its
spectrum and normalized Hilbert--Schmidt distance from `q` are intrinsic.
Direct calculation gives the positive-Gram identity

```text
q-K^*K=(q-V)^*(q-V)/4.                                  (TPH3)
```

Now let `Y` be any global unitary and put

```text
C=pYq,        L=q-C^*C=qY^*(1-p)Yq >=0.                 (TPH4)
```

Normalize the trace and the `L2` norm on `qMq` by `tau(q)`.  If

```text
delta=||C-K||_(2,q),                                    (TPH5)
```

then

```text
||q-V||_(2,q)^2 <= 4 tau_q(L)+8 delta.                  (TPH6)
```

Indeed `(TPH3)` and positivity give

```text
||q-V||_(2,q)^2/4
 =tau_q(q-K^*K)
 <=tau_q(L)+||C^*C-K^*K||_(1,q),
```

and the last norm is at most
`(||C||_(2,q)+||K||_(2,q))delta<=2delta`.

Consequently an authenticated same-corner arithmetic unitary pays the
two-path holonomy with a dimension-independent modulus.  If `C` is unitary
from `q` onto `p`, then `L=0`; exact matching `C=K` forces `V=q`, and
approximate matching gives

```text
||q-V||_(2,q)^2 <= 8 delta.                             (TPH7)
```

The constant and square-root scale are sharp at the scalar level: for
`V=e^(i theta)q`, the distance from `(q+V)/2` to the unit circle is
`1-|cos(theta/2)|`, while `|1-e^(i theta)|^2` is asymptotic to `theta^2`.

There is also an exact universal escape showing why mere compression of a
global group word is insufficient.  For every contraction `K:qH->pH`, the
Julia matrix

```text
J_K = [ K                    (p-KK^*)^(1/2) ]
      [ (q-K^*K)^(1/2)             -K^*     ]            (TPH8)
```

is a unitary from `qH direct_sum pH` to `pH direct_sum qH` (after the
canonical source/range identifications), and its upper-left compression is
exactly `K`.  Applying `(TPH8)` to `(TPH2)` realizes **every** relative
holonomy `V` as the compression of an exact unitary.  In this model

```text
tau_q(L)=||q-V||_(2,q)^2/4.                              (TPH9)
```

Thus the complementary carrier absorbs precisely the cross-term payment.
Fixed amplification supplies the required complements, so neither
conjugate doubling nor a direct-sum sector split removes this escape.

The conclusion is a sharp interface.  Two coherent paths are already enough
analytically; three paths are not intrinsically necessary.  But an ordinary
global unitary word coupled only through its packet compression does not
authenticate the needed corner unitary.  A successful arithmetic/compiler
cell must additionally force `qY^*(1-p)Yq` small (same-corner invariance), or
must charge that positive leakage elsewhere.  Without one of those two
inputs, the two-path cell has an exact finite-dimensional countermodel.

