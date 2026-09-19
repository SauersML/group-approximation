---
rg: 2
id: paid-polar-bridge-does-not-type-moving-hecke-target
kind: claim
title: The paid source polar carries mass but does not type the moving Hecke target
artifacts:
  - research/paid-polar-moving-target-fence-proof.md
distinct_from:
  paid-cut-has-moving-hecke-source-or-detector: that constructs the positive moving source and transports it by a literal Hecke word; this tests whether polar-correcting the earlier paid-source incidence adds the missing source/target Gram and proves that it does not.
  el20-order-seven-heads-force-zero-common-hecke-reducing-cut: that forces an exit from every positive common source cut; this gives an exact acute-angle model in which the polar range is Whitehead-reducing but orthogonal to the Hecke target and the forced exit is paid maximally.
  moving-order-seven-stage-gauges-have-coboundary-drift: that changes gauges between seven moving charts; this isolates the earlier single polar bridge and shows that its relative gauge is analytic rather than ordinary-word authenticated.
  center-chain-common-source-authenticates-native-covariances: that asks for a source-and-target-Gram-typed transition into an unequal native row; this proves the paid polar supplies neither target incidence nor the required fixed-frame gauge lock.
---

**ESTABLISHED SCOPED POLAR FENCE.**  Keep the source branch of
`paid-cut-has-moving-hecke-source-or-detector` and abbreviate

```text
A=EC_sQ_s,       X=A^*A=Q_sC_sEC_sQ_s.
```

If `A=V|A|` is its polar decomposition, then `V` carries
`R_s=supp(X)` into

```text
F_s=supp(EC_sQ_sC_sE)<=E.                              (PPB1)
```

Although `E` reduces both Whiteheads, the subprojection `F_s` need not do
so.

This is a genuine positive analytic bridge.  It does not add an
ordinary-word bridge.  For an ordinary word `a`, the raw authenticated
mixed moment is only

```text
A^*aA=Q_sC_sEaEC_sQ_s,                                 (PPB2)
```

whereas the polar relative coefficient is `V^*aV`.  Passing from `(PPB2)`
to the latter conjugates by the approximation-dependent inverse of `|A|`
on its support.  For either literal Hecke transport `u_i`, the raw
cross-Gram and its polar normalization are

```text
A^*u_i s^(-1)R_s=Q_sC_sEu_i s^(-1)R_s,
V^*u_i s^(-1)R_s=|A|^(-1)A^*u_i s^(-1)R_s.           (PPB3)
```

The first line is the exact ordinary-word-authenticated relative Gram.  No
lower bound on it follows from `A^*A>0`.  The second line contains the
analytic polar and is not the compression of an ordinary word alone.

There is an exact finite-dimensional model of all the abstract operator
data used in this proposed promotion with

```text
||(1-Q)C||_op=1/3<1/2,
X=(8/81)Q,
F<=E,
[E,J_1]=[E,J_2]=0,                                    (PPB4)
```

and two literal unitaries `u_i` satisfying

```text
u_iQu_i^(-1)=P,
v_1=u_1,   v_2=u_2A_1,   t_i=J_iv_i,   t_i^7=1,       (PPB5)
```

but nevertheless

```text
V^*u_iQ=0                 (i=1,2).                    (PPB6)
```

Moreover the polar `V:QH->EH` in this model is an arbitrary prescribed
unitary.  Thus neither its gauge nor even positive overlap with the native
target is fixed by `(PPB4)--(PPB5)`.  The order-seven boundary fence is
respected rather than evaded: for `R_0=Q`,

```text
||(1-R_0)t_iR_0||_2=sqrt(tau(Q)),                     (PPB7)
```

so `10epsilon_1+4epsilon_2>=sqrt(tau(R_0))` holds with ample room.

The frozen ordinary word `s` does not change the conclusion: the model
already uses `s=1`, and conjugating the whole construction gives every
other frozen frame.  Consequently the polar of `EC_sQ_s` may be used as an
analytic carrier alignment, but it cannot be named as a selector transport
or used to compare the quarter/eighth reservoir gauges.  A continuation
still needs an ordinary mixed occurrence with a lower bound on the raw
target Gram in `(PPB3)`, or an independently authenticated fixed-frame
bridge into the unequal native target.

This is a scoped finite-operator countermodel, not a representation of the
full marked `EL_20` coefficient presentation.  It fences only the proposed
formal deduction from the paid source branch, the polar support, the two
literal Hecke transports, and their order-seven heads.  No Property `(T)`,
canonical trace, or literature input is used.

DERIVATION
paid-polar-moving-target-fence-proof
