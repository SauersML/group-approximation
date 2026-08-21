---
rg: 2
id: one-additive-commutator-suffices-for-julia-return
kind: claim
title: One additive commutator suffices for the Julia amplitude return
distinct_from:
  fanizza-heat-return-is-one-cyclic-amplitude-product: that assumes two separately decoded products approximating the marked projection and the heat amplitude; this proves that the scalar contradiction only needs their difference to be one approximate additive commutator.
  trace-cyclic-rank-mismatch-checksum: that compares the traces of two approximate products; this removes the individual product approximations and retains only one commutator residual.
  universal-block-return-violates-the-regular-firewall: that rules out a fixed tracially functorial return; this gives a smaller matrix-only semantic target and explicitly preserves the same firewall.
---

ESTABLISHED.  Fix the Fanizza heat amplitude

```text
B_t=D_R p_t(H_m),
A_t=B_t^*B_t=p_t(H_m)D_Rp_t(H_m).
```

Let `P` be a projection in a finite tracial matrix algebra and let `X,Y` be
arbitrary matrices.  The two-product payload

```text
||YX-P||_2<=epsilon,       ||XY-A_t||_2<=delta
```

implies

```text
||[Y,X]-(P-A_t)||_2<=epsilon+delta,                  (ACJ1)
```

but the latter estimate alone is already enough for the Fanizza return.
Indeed every finite-dimensional additive commutator has trace zero, so

```text
|tr(P)-tr(A_t)|
 =|tr(P-A_t-[Y,X])|
 <=||P-A_t-[Y,X]||_2.                                (ACJ2)
```

On a NONHALT instance the accelerated heat estimate gives

```text
0<=tr(A_t)=||B_t||_2^2<=||B_t||^2<=C_m/(4t^2).
```

Consequently the single semantic estimate

```text
||[Y_t,X_t]-(P-A_t)||_2<=omega(Def)                  (ACJ3)
```

implies

```text
tr(P)<=omega(Def)+C_m/(4t^2),                        (ACJ4)
```

with no bound on `||X_t||` or `||Y_t||` and no constant depending on the
matrix dimension or on `t`.  Thus the constant-sound terminal half of
`dimension-reported-julia-amplitude-return` is over-specified: for its only
downstream use, a self-indexed compiler may return one additive commutator
residual instead of authenticating `YX` and `XY` separately.

## Coefficient-level Steinberg compression

The smaller target has a constant-size algebraic wordization.  In any
unital ring in which the indicated elementary matrices are defined, use the
commutator convention `[g,h]=ghg^(-1)h^(-1)`.  The Steinberg relation gives

```text
[e_12(Y),e_23(X)] [e_12(X),e_23(Y)]^(-1)
   =e_13(YX-XY)=e_13([Y,X]).                          (ACJ5)
```

Therefore `(ACJ3)` is one root-coefficient comparison with
`e_13(P-A_t)`.  In the standard `3 by 3` matrix realization,

```text
||e_13(C)-e_13(D)||_(2,tr_3)=||C-D||_2/sqrt(3),       (ACJ6)
```

so this compression has a dimension- and runtime-independent constant.  It
does not require a growing Clifford multiplication table and it does not
even require two separately authenticated output coefficients.

## Exact boundary

Equations `(ACJ5)--(ACJ6)` are a coefficient-level reduction, not a missing
normalized-HS coefficient decoder for an abstract unitary representation of
a Steinberg group.  That decoder remains the load-bearing groupification
step.  Nor may `(ACJ3)` be imposed as a fixed identity valid in every finite
tracial representation: applying it at zero defect in the regular finite
von Neumann algebra for arbitrarily large `t` would force the nonzero regular
carrier `P` to have trace zero.  The stopping depth and root coefficient
comparison must still be obtained from finite matrix coordinates.  The new
conclusion is only that their terminal semantic payload is one commutator
residual, which is strictly weaker than the previously requested pair of
product residuals.
