---
rg: 2
id: global-triangle-separator-survives-mod-augmentation
kind: claim
title: A global triangle separator survives modulo augmentation and has full-ideal-support finite-dimensional witnesses
distinct_from:
  positive-tree-choi-gap-does-not-force-ideal-support: that shows the canonical tree Fourier defect can be carried wholly by augmentation; this uses a second liftable comparison map to extract an augmentation-zero face defect from the global separator, without claiming that the surviving face is a tree face.
  positive-tree-separator-has-fd-low-ideal-moment-packets: that retains the tree Fourier value but cannot delete the trivial summand; this uses an augmentation-zero observable, deletes that summand quantitatively, and obtains full ideal support.
  km-triangle-relative-gap-failure-has-fd-full-support-witnesses: that gets full-support low-relator packets from failure of relative property T independently of a separator; this correlates full support and low prescribed ideal moments with a positive face Choi value forced by the quotient separator.
---

**ESTABLISHED (mod-augmentation separator and full-support packets).**  Let
`ell` be a normalized quotient separator on the finite-dimensional triangle
operator system `S_Delta`, with gap `delta`, as in `(SQS2)`.  Write

```text
E_epsilon(x)=epsilon(x)1_Q,
D_epsilon=id_(S_Delta)-E_epsilon.                           (MAS1)
```

The scalar map

```text
Phi_epsilon(x)=epsilon(x)1_A
```

is a ucp lift of `E_epsilon`.  Therefore

```text
ell(D_epsilon)>=delta.                                     (MAS2)
```

Moreover `D_epsilon(1)=0` and `epsilon(D_epsilon(x))=0` for every `x`.
If `P_epsilon` denotes postcomposition by `E_epsilon`, then
`D_epsilon` lies in `ker P_epsilon` and `||D_epsilon||<=2`; hence

```text
||ell|_(ker P_epsilon)||>=delta/2.                          (MAS3)
```

Thus the global separator cannot disappear after quotienting the map dual by
augmentation-supported functionals.

Use any fixed bounded face splitting `(SQS7)--(SQS9)`.  Equation `(MAS2)`
gives a face `H in {P_12,P_23,P_13}` such that

```text
ell_H(D_epsilon|_(C^*(H)))>=delta/3.                        (MAS4)
```

The finite-face Choi positivization preserves `(MAS4)` because the defect is
unital-zero.  After normalization it gives a positive Choi state `omega_H`
and an augmentation-zero Choi element `X_H` with

```text
omega_H(X_H)>=c delta>0,                                   (MAS5)
```

where `c` depends only on the three fixed finite faces and the fixed
splitting.

Pull this state to the corresponding matrix amplification of `A=C^*(G_0)`.
For every finite set `Y` in the amplified ideal and every `eta>0`, there is a
finite-dimensional representation packet `rho` and a unit vector `xi` such
that

```text
z_rho=1,
<rho(X_H_tilde)xi,xi> >= (c delta)/2,
sum_(y in Y)||rho(y)xi||^2<eta.                            (MAS6)
```

Here `X_H_tilde` is any self-adjoint lift of `X_H`, and `z_rho` is the unit
of the represented relator ideal.  Unlike the tree-Fourier packet theorem,
the trivial quotient summand can be deleted: every entry of `X_H_tilde` has
zero augmentation, so the observable is identically zero on that summand.

**Sharp scope.**  The face selected in `(MAS4)` need not be one of the two
tree faces; the existing inequalities allow the mod-augmentation component
to sit on the closing face while the tree-Fourier component leaks through
augmentation.  Also `(MAS6)` is still one-vector moment control, not
operator-level Choi feasibility for every packet.  Thus the result closes
the scalar-support leak globally but does not prove uniform triangular ucp
repair or its failure.

Proof: `augmentation-test-deletes-trivial-summand`.

DERIVATION
augmentation-test-deletes-trivial-summand
