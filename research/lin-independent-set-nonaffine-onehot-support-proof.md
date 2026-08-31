---
rg: 2
id: lin-independent-set-nonaffine-onehot-support-proof
kind: route
title: Reduce two-supported independent-set questions to a tracial Boolean 2-CSP
target: lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass
requires:
  - perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model
  - binary-tracial-two-csp-has-classical-solution
---

Fix a trace `tau` on `A_I`.  Pass to its tracial GNS von Neumann
algebra and quotient by the trace kernel, so the induced trace is faithful.
Write

```text
p_(i,v)=pi_tau(e_(i,v)),
S_i={v:p_(i,v)!=0}={v:tau(e_(i,v))>0}.                 (LNP1)
```

The `p_(i,v)` form a PVM for every `i`.

Suppose for contradiction that `|S_i|<=2` for every question.  Turn each
supported outcome menu into one Boolean variable.  If `S_i={v_i}`, put

```text
P_i^0=1,                    P_i^1=0
```

and pin the classical value to zero.  If
`S_i={v_i^0,v_i^1}`, put

```text
P_i^a=p_(i,v_i^a),          a in F_2.                  (LNP2)
```

For each pair of independent-set questions retain precisely the supported
answer pairs which win `I`; this is an arbitrary Boolean binary relation.
A losing supported pair gives

```text
P_i^a P_j^b=0.                                      (LNP3)
```

If both variables are nonconstant, one relation `(LNP3)` already makes
the two endpoint PVMs commute: the two projections in `(LNP3)` are
orthogonal, hence commute, and replacing either by its complement preserves
commutation.  If an endpoint is pinned, it commutes automatically.  A full
binary relation needs no constraint.  Therefore `(LNP2)--(LNP3)` are an
exact operator solution, in a finite tracial von Neumann algebra, of a
Boolean unary-binary CSP.

By `binary-tracial-two-csp-has-classical-solution`, that CSP has a
deterministic satisfying assignment.  Choosing the corresponding supported
vertex for every independent-set question avoids every losing pair and gives
a perfect classical strategy for `I`.  This contradicts
`omega_*(I)<1`.  Hence

```text
some i has |S_i|>=3                                    (LNP4)
```

for every trace `tau`.

Now define `r_i` and `eta` as in `(LNO2)`.  Because the outcome set is
finite,

```text
sum of the two largest w_(i,v)
  =max_(u!=v)(w_(i,u)+w_(i,v)),                         (LNP5)
```

so `r_i` and `eta` are continuous affine-coordinate expressions followed
by finite maxima.  The tracial state space `T(A_I)` is compact.  Statement
`(LNP4)` says `eta(tau)>0` at every point, so the attained minimum

```text
eta_0=min_(tau in T(A_I)) eta(tau)                      (LNP6)
```

is strictly positive.  This proves the uniform assertion.

For the affine obstruction, identify a one-hot outcome `v` with the unit
vector `delta_v` in the Boolean cube.  Three distinct supported outcomes
give

```text
delta_u+delta_v+delta_w in Aff_F2({delta_s:s in S_i}),  (LNP7)
```

because an affine hull over `F_2` contains every odd sum of its points.
The vector in `(LNP7)` has Hamming weight three and violates the one-hot
predicate.  Thus no trace satisfies the local affine-safety hypothesis.

More generally, let a proposed local LCS gadget use visible bits `x` and
scalar auxiliary bits `y`.  Its scalar solutions form an affine set
`Z subseteq F_2^(x,y)`, and its visible projection `pr_x(Z)` is affine.
If every positive atom `delta_s` has an auxiliary extension, then

```text
Aff_F2({delta_s:s in S_i}) subseteq pr_x(Z),             (LNP8)
```

so `(LNP7)` survives.  This proves the atomwise scalar-extension no-go.
The argument does not apply to a shared noncommuting ancillary sector which
does not reduce on the individual one-hot atoms; that is exactly the
remaining global possibility.

Finally suppose a finite LCS `L` has a decoder taking every perfect
Connes-embeddable state to a perfect Connes-embeddable state of `I`.
All traces of `A_I` are non-Connes-embeddable, so no such perfect state of
`L` exists.  The finite `qa` correlation set is compact and the payoff is
continuous; therefore `omega_qa(L)<1`.  If, on finite-dimensional
strategies, the stronger loss inequality `(LNO5)` holds, then with
`delta_I=1-omega_*(I)>0`,

```text
delta_I <= Loss_I(Decode(S)) <= C Loss_L(S),            (LNP9)
```

and taking the infimum proves `(LNO6)`.  This is the exact quantitative
condition; an unaccompanied exact satisfiability map supplies no such bound.
