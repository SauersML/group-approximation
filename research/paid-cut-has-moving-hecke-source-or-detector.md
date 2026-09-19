---
rg: 2
id: paid-cut-has-moving-hecke-source-or-detector
kind: claim
title: Paid Whitehead mass either pays a detector or enters one moving Hecke source row
artifacts:
  - research/paid-moving-hecke-source-proof.md
distinct_from:
  paid-t00-reynolds-cut-is-whitehead-reducing: that produces paid mass on a cut reducing both prefix Whiteheads but does not compare that cut with the signed Hecke source; this makes the comparison after conjugating the source by the frozen paid word.
  paid-t00-carrier-has-signed-hecke-reynolds-dichotomy: that is an operator-norm source-or-detector alternative with no trace mass; this combines its source branch with the paid Whitehead trace overlap and then applies one literal Hecke word.
  el20-order-seven-heads-force-zero-common-hecke-reducing-cut: that rules out a positive common reducing subcut of the fixed signed source; this constructs a positive moving source cut and quantifies the order-seven exit which it must pay.
  center-chain-common-source-authenticates-native-covariances: that asks to identify both common-source Hecke maps with the actual unequal native selector covariances; this reaches the exact common Hecke source and one literal Hecke transport but deliberately does not make that missing identification.
  row2-source-factor-detects-paid-pauli-sheet: that gives a literal word detecting the two paid Pauli sheets but no signed-source incidence or boundary estimate; this obtains signed-source mass under the detector alternative but does not type its common Hecke target as the unequal native row.
  paid-polar-bridge-does-not-type-moving-hecke-target: that polar-corrects the positive operator in this claim and proves the resulting analytic isometry can have zero Gram with both literal Hecke targets and arbitrary gauge, even under the strict source-incidence branch and exact order-seven heads.
---

**ESTABLISHED MOVING-SOURCE ALTERNATIVE.**  Freeze the paid menu member from
`paid-t00-reynolds-cut-is-whitehead-reducing`.  Thus, for one ordinary word

```text
s=w u_epsilon^(-1),        C_s=sCs^(-1),
```

there is a projection `E` reducing `J_1,J_2` such that

```text
alpha=tau(EC_sE)>=tau(P_z)/7936.                       (PMH1)
```

Conjugate the actual signed source and its detector menu by the same word:

```text
Q_s=sQs^(-1),       r_(g,s)=s r_g s^(-1),
b_s=max_(g in L_0)||(r_(g,s)-1)C_s||_op.              (PMH2)
```

There is an exact alternative.  Either

```text
b_s>=1/2,                                                   (PMH3)
```

so one fixed conjugated ordinary detector word pays on the frozen paid
carrier, or else the positive contraction

```text
X_s=Q_s C_s E C_s Q_s                                  (PMH4)
```

satisfies

```text
tau(X_s)>=(1-b_s^2)alpha
        >3tau(P_z)/31744.                               (PMH5)
```

Let `R_s=supp(X_s)<=Q_s`, put `R_0=s^(-1)R_ss<=Q`, and retain the two exact
common-source Hecke words

```text
u_1=B_2A_1,             u_2=B_3A_2A_1.
```

For either chosen row `i`, the ordinary word `u_i` carries the positive cut
`R_0` with no boundary:

```text
R_i=u_iR_0u_i^(-1)<=P,
(1-R_i)u_iR_0=0,
tau(R_0)>=tau(X_s)>3tau(P_z)/31744.                    (PMH6)
```

Thus the source branch really does transport paid Whitehead mass through
one actual common-source Hecke occurrence.  It uses moving cuts: `E`,
`R_s`, `R_0`, and `R_i` are not asserted equal or jointly reducing.

That qualification is forced, not cosmetic.  For

```text
t_1=J_1B_2A_1,             t_2=J_2B_3A_2,
epsilon_i=||(1-R_0)t_iR_0||_2,
```

the exact incompatible-character commutator gives the finite boundary
fence

```text
10epsilon_1+4epsilon_2>=sqrt(tau(R_0)),                (PMH7)
max(epsilon_1,epsilon_2)>=sqrt(tau(R_0))/14.           (PMH8)
```

In particular this positive source cut cannot be recycled as one common
order-seven reducing cut.  A continuation must use a genuinely different
next cut and pay/authenticate that transition.

The result stops exactly before the unequal native selector seam.  On the
refined source `Q`, both Hecke words land in the same range `P`; the
quarter/eighth flag data have not been identified with the two actual native
selector outputs.  One row also admits a multiplicity coboundary which can
be absorbed into the next moving chart.  What is missing is an ordinary
odd-parity transition from `R_i` to the next coefficient-typed cut, with its
source and target Grams fixed in the Hecke frame (or an ordinary relation
which makes `(PMH3)` pay presentation defect).  Neither a common invariant
cut nor the tautological conjugate `t_iR_0t_i^(-1)` supplies that datum.
For the literal row-two candidate, the already detected sheet face reduces
this further to a quantitative `S_57` boundary/source-incidence transition;
detecting its nonzero root globally is not yet control on `R_i`.

Polar-decomposing `EC_sQ_s` also does not supply the missing datum.
`paid-polar-bridge-does-not-type-moving-hecke-target` records the exact raw
ordinary-word Gram which survives that operation and gives an acute graph
model in which the polar support is full but its Gram with both `u_i`
targets is zero.

No Property `(T)`, canonical trace profile, or fixed common invariant cut is
used.

DERIVATION
paid-moving-hecke-source-proof
