---
rg: 2
id: two-positive-cross-fusion-carrier-audit-proof
kind: route
title: Track both complementary cross fusions on their literal Hecke carriers
target: two-positive-cross-fusions-leave-selector-seam
requires:
  - fused-cross-returns-cancel-positive-l0-gauge
  - cross-whitehead-sandwiches-branch-roots-into-signed-normalizer
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
  - individual-cross-whiteheads-miss-native-hecke-target
  - same-center-whitehead-gram-is-not-native-selector-gram
---

Apply `(CWR6)--(CWR7)` first to `(g_0,g_1)=(r,p)` and then to
`(g_0,g_1)=(q_1,q_0)`.  The coefficient products are respectively

```text
(pr,rp)=(q_0,q_1),             (pq_1,rq_0)=(p,r),
```

which proves all four conjugations.  Root-subgroup addition and
`q_0+q_1=1` prove both fusions.  The arrows `6->7` and `6->8` occur as
positive generators in `(ERN1)`, proving their identity action on `Q`.
The output roots in `(TPF3)` preserve `Q` by `(CWR8)`, so restriction of
their product gives `(TPF5)`.

The two `K_i` commute and their product is `T`.  For each branch root in
`(TPF1)`, the complementary `K` commutes with that root.  Hence

```text
TA_iT=K_iA_iK_i=B_i.
```

Conjugating `(TPF5)` by `T` proves `(TPF6)`.  The same block calculation
for the coefficient one root gives `(TPF7)`.

Since `L_i=K_iA_i`, involutivity gives
`P=A_1K_1K_0A_0=A_1TA_0`; multiplication on the left by `T=T^(-1)` gives
`B=TA_1TA_0=B_1A_0`, proving `(TPF6b)`.  In the block for `K_0`, the first
column is `(q_1,r)^t`.  Multiplication by the coefficient `q_1` leaves only
the `q_1` entry because `rq_1=0`; hence

```text
K_0x_76(q_1)K_0=x_76(q_1).
```

Together with `K_0A_0K_0=B_0`, this gives
`K_0BK_0=B_1B_0=x_76(1)`.  Its positive character on `Q` proves
`BQ_0=Q_0`, and hence the equality of the direct and composite paths on
`Q_0`.

On coordinates `(7,8)`, `T=w_78(u)` has block
`[[0,u],[u,0]]`.  Conjugating `h=x_28(1)` reads the second row of this
block and gives `x_27(u)`.  Since `u=p+r` is a nonconstant reduced Leavitt
expression and every member of `L_0` has entries in the embedded `F_2`,
this element is outside `L_0`.  This proves `(TPF8)` and prevents transfer
of the positive `x_86(1)` typing from `Q` to `Q_T`.

For `(TPF9)`, `d_0,d_1` are commuting involutions.  Every conjugation of
an identity branch factor is identity, all fusions are identity, and the
only aggregate equation is `T=d_0d_1`.  Thus the assignment verifies the
whole displayed reservoir table while retaining both individual factors.
The literal coefficient and root-position comparison in `(TPF10)` then
isolates the remaining native occurrence seam.  The direct-product
extension is valid at the level of the displayed scoped gauge equations
because no `J_i` or `v_i` variable occurs in any of `(TPF1)--(TPF9)`;
`(IKT5)` independently forbids identifying a `K_i` chart with the native
`J_1` chart.
