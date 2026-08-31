---
rg: 2
id: schur-toeplitz-head-swap-exposes-the-steinberg-injectivity-fork
kind: claim
title: The odd-characteristic Schur Toeplitz head is finitely actuated, but finite presentation still needs Steinberg shift injectivity
distinct_from:
  toeplitz-tail-plus-one-swap-generates: that proves the characteristic-two formula `1+e_0+e_1+a+b` for the bare binary Toeplitz ring; this supplies the sign-corrected actuator over the odd splitting field required by the Schur packet and audits the resulting Steinberg/elementary finite-presentation fork.
  schur-toeplitz-envelope-has-proper-self-embedding: that proves injectivity of the coefficient-ring endomorphism and of its elementary-matrix realization; this identifies why ring injectivity does not by itself prove injectivity on the finitely presented Steinberg cover.
  schur-packet-head-actuator-generates-over-tail: that gives the intended packet/elementary generation statement; this repairs its characteristic mismatch and separates generation from faithful finite-presentation syntax.
  tail-wordized-child-surplus-collision-supplies-rct7: that proves soundness once recursive carrier reflections are ordinary words; this audits which of those words the Schur Toeplitz nodes actually provide.
---

**ESTABLISHED AUDIT.**  The existing Schur--Toeplitz nodes do not yet supply
the finitely presented recursive syntax assumed by the corrected-child
collision.  Head generation is repairable by one exact sign correction.  The
first remaining algebraic identity is

```text
ker(St_5(sigma):St_5(R_f)->St_5(R_f))=1.              (SFI1)
```

It is not a consequence of the established injectivity of
`sigma:R_f->R_f`.

## The odd-characteristic head actuator

Use the packet-headed ring `R_f` and write

```text
P=P_f,       e_1=xPy,       a=xP,       b=Py.
```

These are the four matrix units of the first two Toeplitz coordinates.  Over
the fixed odd splitting field define

```text
s_f=1-P-e_1+a+b.                                      (SFI2)
```

Then exactly

```text
s_f^2=1,                 s_f e_1 s_f=P.               (SFI3)
```

Indeed `s_f` is the transposition `a+b` on the two-dimensional head and the
identity on its complement.  This is the characteristic-independent formula.
The formula `1+P+e_1+a+b` in
`toeplitz-tail-plus-one-swap-generates` agrees with it only in
characteristic two and is generally not an involution over the odd Schur
splitting field.

The corrected actuator still generates the head over the tail.  Since

```text
a=e_1 s_f P,                 b=P s_f e_1,              (SFI4)
sigma(x)=x^2y+P,             sigma(y)=xy^2+P,
x=x^2y+a,                    y=xy^2+b,                 (SFI5)
```

we get

```text
x=sigma(x)-P+a,              y=sigma(y)-P+b.           (SFI6)
```

Consequently

```text
R_f=<sigma(R_f), k[B_f], s_f>.                         (SFI7)
```

Thus only finitely many packet coefficients and one bounded head actuator
are needed.  Steinberg addition and commutator relations turn `(SFI7)` into
a fixed finite root-word menu after choosing spare indices.

## The finite-presentation fork

The established results now form the following strict fork.

```text
EL_5(R_f):   sigma is injective on matrices,
             but finite presentation of EL_5(R_f) is not proved;

St_5(R_f):   finite presentation follows from Krstic--McCool,
             but injectivity of St_5(sigma) is not proved.              (SFI8)
```

The compression `a |-> yax` does not close `(SFI1)`.  It is the inverse ring
map on the subring `sigma(R_f)`, but on all of `R_f`

```text
(yax)(ybx)=ya(xy)bx=ya(1-P)bx,                         (SFI9)
```

which need not equal `yabx`.  Hence it is not a ring retraction
`R_f->R_f`, and functoriality gives no left inverse to `St_5(sigma)`.
Equivalently, inclusion of a coefficient subring can acquire a kernel on
Steinberg `K_2` even when the coefficient inclusion is injective.

An ascending-HNN presentation on a finite Steinberg generating set can be
written with finitely many relators whether or not `(SFI1)` holds.  But
Britton embedding of the base, and therefore survival of the marked Schur
word in the exact completeness model, requires the endomorphism to be
injective.  Conversely the elementary HNN has the required faithful base but
only the finitely generated recursive presentation already recorded in
`schur-toeplitz-root-mark-is-fd-invisible`.  Higman embedding does not repair
this syntax for the quantitative argument, because it supplies no uniform
normalized-HS derivation bound for the recursive collision words.

## The next word identity after `(SFI1)`

The raw Toeplitz defect does have a reflection word on the Steinberg side.
For

```text
e_n=sigma^n(P),              u_n=1-2e_n,               (SFI10)
```

`u_n^2=1`, and the standard torus word

```text
h_ij(u_n)=w_ij(u_n)w_ij(-1)                            (SFI11)
```

maps to a two-coordinate diagonal copy of `u_n` in the elementary quotient.
Thus the odd characteristic and the passage from an idempotent to a literal
reflection are not intrinsic obstacles.

What is not established is that this raw defect reflection is the aggregate
corrected-child reflection `R_(C,n)` of `(TSC7)`.  The current Schur root word
`x_12(P_f)` records an oriented unipotent coefficient, while the collision
uses the full child projection satisfying

```text
tr(C_n)>=tr(Q_n)+v_n.                                  (SFI12)
```

No existing identity identifies `C_n` with `e_n`, or with a fixed matrix
amplification of `e_n`, while retaining the shared noncommuting BCS contexts.
Accordingly the precise dependency bridge is:

```text
odd head actuator (SFI2)--(SFI7)              ESTABLISHED
finite Steinberg presentation                 ESTABLISHED
Steinberg shift injectivity (SFI1)            OPEN
corrected-child coefficient/reflection word   OPEN
collision estimate (TSC5)--(TSC11)            ESTABLISHED.   (SFI13)
```

This separates two syntactic obligations from the already completed scalar
soundness argument.  Neither `toeplitz-tail-retains-contextual-schur-density`
nor the proper coefficient self-embedding silently supplies them.
