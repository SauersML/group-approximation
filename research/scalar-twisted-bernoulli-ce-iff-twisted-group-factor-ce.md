---
rg: 2
id: scalar-twisted-bernoulli-ce-iff-twisted-group-factor-ce
kind: claim
title: A scalar-twisted Bernoulli crossed product of a residually finite group is CE exactly when its twisted group algebra is CE
distinct_from:
  sp4-isw-theorem-c-embeddable-twist-data-exists: that asks for a sequence of operator-valued cocycles satisfying the ISW hypotheses; this proves the complete Connes-embeddability toll for the constant scalar cocycles over the Bernoulli action.
  nonce-twisted-factor-gives-nonhyperlinear-group: that converts a non-CE twisted group algebra to a nonhyperlinear central extension; this identifies when adjoining a classical Bernoulli base changes Connes embeddability.
---

**ESTABLISHED.** Let `Gamma` be a countable residually finite group, let
`c in Z^2(Gamma,T)` be a normalized scalar cocycle, and let `Gamma` act by
the Bernoulli shift on a standard probability space

```text
(X,mu)=(X_0,mu_0)^Gamma.
```

Then

```text
L^infty(X) x|_c Gamma is Connes embeddable
    iff
L_c(Gamma) is Connes embeddable.                         (TBC1)
```

Here the group unitaries in the crossed product obey
`u_g u_h=c(g,h)u_(gh)`, and `L_c(Gamma)` denotes the corresponding twisted
group von Neumann algebra with its canonical trace.

The forward implication is immediate: the twisted group unitaries generate
a trace-preserving copy of `L_c(Gamma)` inside the crossed product, and
Connes embeddability passes to von Neumann subalgebras.

For the converse, use the tracial-microstate criterion. Fix a finite mixed
word window in the algebraic crossed product. Approximate every base
coefficient in that window by a cylinder function on a finite coordinate
set `D subset Gamma`. Approximate the finite-dimensional distribution of
the base values by a rational atomic probability space, then realize that
space as a quotient of a finite uniform alphabet `A`.

Residual finiteness supplies a finite quotient `q:Gamma->Q` that is
injective on the finite multiplication/coordinate window needed to
distinguish all selected translates of `D`. On

```text
K_Q = l^2(A^Q)
```

represent the selected cylinder functions by diagonal multiplication
operators and let `P_(q(g))` be the permutation unitary implementing the
Bernoulli shift of `Q`.

Connes embeddability of `L_c(Gamma)` supplies, on another finite-dimensional
space, projective microstates `V_g` satisfying on the selected window

```text
V_g V_h approximately c(g,h)V_(gh),
tr(V_g) approximately 0                  (g != 1).       (TBC2)
```

Put

```text
W_g = V_g tensor P_(q(g)).                               (TBC3)
```

The first tensor factor gives the scalar-twisted multiplication law, while
the second implements the selected Bernoulli covariance relations exactly.
After reducing any selected mixed word, its matrix trace has the form

```text
tr(V_k) tr(D_f P_(q(k))).                                (TBC4)
```

If `k != 1`, the first factor tends to zero by `(TBC2)`, exactly as required
by the crossed-product trace. If `k=1`, the first factor is one and the
second factor is the finite Bernoulli integral of the resulting cylinder
function; local injectivity of `q` makes this agree with the original
Bernoulli integral on the prescribed window, up to the initial atomic
approximation. Multiplication and adjoint defects are controlled in the
same way. Enlarging the windows and taking a diagonal sequence gives
tracial matrix microstates for the crossed product, proving `(TBC1)`.

Thus a constant scalar twist over a Bernoulli action creates no additional
Connes-embeddability problem once the acting group has locally injective
finite quotients. In particular, for `Sp_4(Z)` the ISW Theorem-C
embeddability toll for the constant Maslov cocycles is exactly the CE status
of the corresponding Maslov-twisted group von Neumann algebras.

