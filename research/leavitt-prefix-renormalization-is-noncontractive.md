---
rg: 2
id: leavitt-prefix-renormalization-is-noncontractive
kind: claim
title: Leavitt prefix renormalization does not contract supremal additive-root defect
distinct_from:
  iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart: that proves the exact ring isomorphism and its matrix units; this computes its effect on the uniform additive-defect norm and exhibits a stationary recursive leak.
  leavitt-prefix-boundaries-do-not-split-additive-character-mass: that gives one genuinely additive character detecting every prefix; this uses nonlinear p-phase root tables whose additive defect stays fixed while its witness moves to arbitrary depth.
  single-affine-leavitt-branch-chart-is-stationary: that gives finite marked representations of an isolated finite HNN chart; this is a direct defect-renormalization theorem on the infinite active coefficient space.
  diagonal-leavitt-prefix-transport-cannot-carry-cross-corners: that proves off-diagonal prefix compression is not multiplicative; this shows that even the valid diagonal compression has contraction factor exactly one for remote additive defects.
---

Let `B=ARA` be the active corner of the relative binary Leavitt envelope and
put

```text
P(r)=t_0 r s_0,             alpha(r)=s_0 r t_0.          (LNR1)
```

Both maps are additive and

```text
P alpha=id_B.                                             (LNR2)
```

For a map `f:B->U(d)` with `f(0)=I`, define its uniform additive defect

```text
D(f)=sup_(a,b in B)||f(a+b)-f(a)f(b)||_2.                (LNR3)
```

Then

```text
D(f compose P^n)=D(f)                  for every n>=0.   (LNR4)
```

The upper bound follows because `P^n` is additive; the lower bound follows
because it is surjective with section `alpha^n`.  Moreover

```text
(f compose P^(n+1))(alpha(r))=(f compose P^n)(r),        (LNR5)
```

so the same defect witness is transported one prefix level deeper at each
step.  This is an exact recursive moving-word leak.

There are nontrivial exponent-`p` examples.  Choose independent linear
functionals `ell_1,ell_2:B->F_p`, a primitive `p`th root `zeta`, and set

```text
f(r)=zeta^(ell_1(r) ell_2(r)).                           (LNR6)
```

Then `f(r)^p=1`, but for suitable `a,b`,

```text
f(a)=f(b)=1,       f(a+b)=zeta,
D(f)>=|zeta-1|.                                           (LNR7)
```

Equations `(LNR4)--(LNR5)` keep this floor unchanged at arbitrary prefix
depth.  Replicating the phase onto both diagonal children does not help: the
map obtained by summing the two child exponents restricts to the original
`f` on either diagonal corner, so its defect is still at least `(LNR7)`.

The mixed Steinberg transfer also has no hidden contraction.  With the
notation of `mixed-steinberg-triangles-transfer-actor-additivity`, let
`D_X` be the actor-root additive defect, `M` the uniform mixed-triangle
decoding defect, and `C` the centralizing defect.  The same five-step
commutator calculation gives

```text
D_Y <= 2 D_X+3 M+C.                                      (LNR8)
```

The upstream coefficient is `2`, not a number below one.  Iterating around
root indices or through prefix charts therefore transfers a uniform bound
once one is known, but cannot create it by contraction.

This does not construct an almost representation of the full Steinberg
presentation: the nonlinear phases in `(LNR6)` deliberately violate the
remote additive actor-root rows.  It proves the exact limitation of the
proposed renormalization argument.  The algebraic isomorphism
`B isomorphic to M_2(B)`, diagonal branch conjugacies, and Steinberg
commutator expansion alone admit a stationary deep leak.  A positive proof
needs an additional same-carrier square-function estimate which charges all
four matrix entries and has a genuine return coefficient `lambda<1`; no
such estimate follows from Leavitt self-similarity itself.

