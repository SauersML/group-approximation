---
rg: 2
id: rational-group-corner-map-forces-rational-regular-trace
kind: claim
title: A rational algebraic group-corner model carries a rational-valued regular trace
distinct_from:
  oracular-2csp-algebraic-corner-map-is-a-canonical-groupifier: that uses the normalized canonical corner trace to obtain a CE game model under hyperlinearity; this records an unconditional arithmetic restriction on that trace before any approximation hypothesis is made.
  injective-group-corner-map-requires-faithful-trace: that uses injectivity to force faithfulness of a pulled-back trace; this needs no injectivity and instead proves rationality of every rational moment.
  augmentation-one-corner-retains-a-character: that composes with augmentation when the corner has augmentation one; this uses the canonical regular trace and applies equally to augmentation-zero corners.
---

**ESTABLISHED.**  Let `A_Q` be a unital rational star algebra, let `Gamma`
be a countable group, and suppose

```text
0!=q=q^*=q^2 in Q[Gamma],
Phi:A_Q -> q Q[Gamma] q,             Phi(1)=q             (RRT1)
```

is a unital star homomorphism.  Then

```text
sigma(a)=tau_Gamma(Phi(a))/tau_Gamma(q)                  (RRT2)
```

is a rational-valued tracial state on `A_Q`:

```text
sigma(A_Q) subset Q,          sigma(a^*a)>=0.             (RRT3)
```

After complexification, `(RRT2)` is a positive normalized trace on
`A_Q tensor_Q C`.  In particular, every rational projection in `A_Q` has
rational `sigma`-mass.  No hyperlinearity or injectivity assumption is used.

Consequently, if a rational game star algebra has no rational-valued tracial
state, it admits no nonzero unital map into a rational algebraic corner of
**any** group.  More generally, a proposed construction must produce much
more than a rational point of the local marginal polytope: it produces one
trace whose value on every rational word in the game generators is rational.

There is an exact weighted word-problem formula.  Write

```text
q=sum_(h in F_0)c_h h,
Phi(y_i)=sum_(g in F_i)c_(i,g) g                         (RRT4)
```

with rational coefficients.  For every rational star word `w` in the
generators, expand `Phi(w)=sum_g c_(w,g)g` after collecting equal group
elements.  Then

```text
sigma(w)=c_(w,1)/c_(q,1).                               (RRT5)
```

Thus the whole pulled-back trace is a normalized identity-coefficient
counting trace on the finitely generated support subgroup.  A matrix-corner,
finite-packet, or graph-of-groups proposal which only realizes the local
projection equations in a chosen representation has not constructed
`(RRT1)` unless these coefficient identities already hold in the abstract
group algebra.

The condition is necessary, not sufficient.  A rational-valued trace need
not be Connes embeddable and need not admit a projective group basis; the
latter is precisely the remaining group-corner construction problem.

The restriction is genuine even for a one-generator finitely presented
rational star algebra.  Put

```text
C_Q=Q<y=y^* | y^4=2>.
```

It has positive representations, for example `y |-> 2^(1/4)`.  In every
positive star representation, spectral calculus for the self-adjoint
operator `y` gives

```text
y^2=sqrt(2) 1.
```

Hence every tracial state on its complexification satisfies
`sigma(y^2)=sqrt(2)` and is not rational-valued on `C_Q`.  Therefore `C_Q`
cannot map unitaly into a nonzero rational group-algebra corner.  Merely
knowing that a rationally presented star algebra has a positive tracial model
does not supply the arithmetic trace demanded by `(RRT1)`.
