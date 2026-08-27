---
rg: 2
id: leavitt-noncontractive-root-defect-proof
kind: route
title: Pull a quadratic phase through the surjective prefix extraction
target: leavitt-prefix-renormalization-is-noncontractive
requires: []
---

The Leavitt relations give

```text
P(alpha(r))=t_0(s_0 r t_0)s_0
           =(t_0s_0)r(t_0s_0)=ArA=r,                  (LNP1)
```

proving `(LNR2)`.  If `g=f compose P^n`, then additivity of `P^n` gives

```text
||g(a+b)-g(a)g(b)||_2
 <=D(f),                                                (LNP2)
```

so `D(g)<=D(f)`.  Conversely, lift any pair `(x,y)` through the section:

```text
a=alpha^n(x),        b=alpha^n(y).
```

The defect of `g` at `(a,b)` is exactly the defect of `f` at `(x,y)`.
Taking suprema proves `(LNR4)`, and `(LNR5)` is the same calculation with
one fewer iterate.

The additive group of `B` is an infinite-dimensional `F_p`-vector space, so
choose `a,b` and linear functionals with

```text
ell_1(a)=1, ell_2(a)=0,
ell_1(b)=0, ell_2(b)=1.                                 (LNP3)
```

The quadratic phase `(LNR6)` then gives `(LNR7)`.  It is scalar-valued, so
spectator amplification or passage to a larger matrix dimension changes
neither the defect nor its carrier density.

For symmetric diagonal replication, define

```text
q'(r)=q(t_0rs_0)+q(t_1rs_1),
f'(r)=zeta^(q'(r)).                                     (LNP4)
```

On `alpha_i(r)=s_i r t_i`, dual-prefix cancellation gives

```text
q'(alpha_i(r))=q(r).                                    (LNP5)
```

Hence either child contains a lifted copy of the old defect witness.  This
rules out the hope that merely checking both diagonal children supplies a
strict factor.

Finally repeat the proof of the mixed Steinberg transfer while retaining
separate error parameters.  Replacing `Y(a+b)` and the two decoded
commutators costs `3M`; replacing `X(a+b)` inside a commutator costs
`2D_X`; removing the conjugation costs `C`.  This proves `(LNR8)`.

The dual-prefix matrix chart contains four entries, not two.  Controlling
them by orthogonal carriers can at best give an unweighted square sum of
their errors.  Taking a supremum over coefficient pairs supplies no
normalizing factor, and `(LNP4)--(LNP5)` already prevent any universal
factor below one.  A contractive recurrence must therefore use a new
positive-density common return, not the matrix chart's additive bijection.

