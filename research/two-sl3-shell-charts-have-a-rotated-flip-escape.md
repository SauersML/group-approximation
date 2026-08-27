---
rg: 2
id: two-sl3-shell-charts-have-a-rotated-flip-escape
kind: claim
title: Two noncommuting SL3 shell charts admit an exact rotated-flip transporter escape
distinct_from:
  two-equivariant-shell-pvms-have-independent-coordinate-escape: That uses two commuting coordinate PVMs and no chart transporter; this rotates one chart to make the pair noncommuting and supplies an exact full off-diagonal transporter.
  central-hecke-controlled-multipaths-remain-sectorwise: That assumes one central control chart; this shows that even leaving the central class for two noncommuting charts and one matched block does not yet create holonomy.
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: That uses the actual denominator section identities; this is a sharp no-go for abstract two-chart covariance and transporter fullness before those raw identities are imposed.
---

# Two noncommuting SL3 shell charts admit a rotated-flip escape

Put

```text
C=SL_3(Z),       D=C intersect hCh^(-1),
Omega=C/D,       |Omega|=42.
```

On `H=l^2(Omega times Omega)`, let `rho(C)` act diagonally, let `P_i` and
`Q_i` be the first- and second-coordinate PVMs, and let

```text
F delta_(x,y)=delta_(y,x).
```

Then `F` commutes with `rho(C)` and `FQ_iF=P_i`.  For
`0<t<pi/2`, set

```text
U_t=cos(t) I+i sin(t)F,       Q_i(t)=U_t Q_i U_t^*.     (RTF1)
```

The two PVMs `(P_i)` and `(Q_i(t))` are both exactly covariant for the same
`C`-action and are genuinely noncommuting.  Nevertheless, for any `g in C`,

```text
V_(g,t)=rho(g) F U_t^*,
V_(g,t) Q_i(t) V_(g,t)^*=P_(g i).                       (RTF2)
```

Thus every matched off-diagonal block is source- and range-full:

```text
X_i=P_(g i)V_(g,t)Q_i(t)=V_(g,t)Q_i(t),
X_i^*X_i=Q_i(t),                 X_iX_i^*=P_(g i).      (RTF3)
```

The transporter is compatible with the actor up to the inner relabeling
`g`:

```text
V_(g,t)rho(c)V_(g,t)^*=rho(gcg^(-1)).                   (RTF4)
```

Despite this exact same-carrier incidence, the untransported corresponding-
atom overlap remains far from saturation.  With normalized trace,

```text
tr(P_i Q_i(t))=cos(t)^2/42^2+sin(t)^2/42,

Delta(t)=sum_i (1/42-tr(P_iQ_i(t)))
        =(41/42)cos(t)^2.                               (RTF5)
```

Hence for every fixed `t` strictly between `0` and `pi/2`, the two charts are
noncommuting, all matched blocks `(RTF3)` are exact, all actor covariance
relations are exact, and the chart mismatch is still a fixed positive
constant.

The model also admits canonical-character camouflage for the group actually
tested here.  The relation `(RTF4)` presents an inner semidirect product,
hence a copy of `C times Z` after replacing the stable letter by
`rho(g)^*V_(g,t)`.  Tensor `rho(c)` with deep regular congruence
representations of `C`, and tensor `V_(g,t)` with the corresponding regular
matrix for `g` and a cyclic regular shift of order tending to infinity.
Every fixed nontrivial word then has trace tending to zero, while
`(RTF2)--(RTF5)` are unchanged.

This is a scoped two-chart no-go.  The operator `V_(g,t)` is not asserted to
be the image of the arithmetic denominator generator; the raw section
identities in `raw-denominator-incidence-kills-off-diagonal-shell-orbit` are
exactly the additional arithmetic data omitted here.  Therefore one abstract
off-diagonal block, even if full and actor-equivariant, cannot prove the
needed trace-square payment.

The first gauge-invariant candidate is a closed three-chart comparison.  For
three PVMs `P,Q,R` with transports `V_PQ,V_QR,V_RP`, the compressed loop

```text
P_i V_PQ Q_j V_QR R_k V_RP P_i                         (RTF6)
```

retains a conjugacy-invariant holonomy on the `P_i` corner.  Equivalently,
rank-one charts carry the Bargmann scalar `tr(P_iQ_jR_k)`, whose phase is
invisible to every two-projection principal-angle decomposition.  A useful
arithmetic triangle must authenticate two competing return paths (or their
additive difference); one loop by itself can still be absorbed in a
multiplicity gauge.

The three-chart audit is now exact as well.
`three-chart-loop-retains-free-multiplicity-holonomy` identifies the
Bargmann/loop trace as the first gauge invariant, but shows that a spectator
multiplicity unitary realizes it arbitrarily.  The useful datum is therefore
not merely a triangle: it is a native relation comparing two returns in the
same corner.
