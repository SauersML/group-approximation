---
rg: 2
id: atlas-a4-four-cycle-dirichlet-compiler
kind: claim
title: One scalar four-transvection Dirichlet energy is enough to compile the A4 atlas
artifacts:
  - experiments/atlas_a4_classical_two_holonomy_profile.py
  - experiments/atlas_a8_four_cycle_raw_s3.py
  - experiments/atlas-word-19243.json
distinct_from:
  atlas-a4-four-cycle-trace-compiler: that stronger target transfers the collision trace separately to three leaf traces; this target asks only for the final sum of four trace deficits.
  atlas-a4-relative-packet-commutator-collapse: that stronger target controls ten packet-letter commutators; this target controls only the minimal four-transvection generating cycle.
---

For the normalized exact-regular A4 context network, let

```text
T={t01,t12,t23,t30},
V_n(t)=U_n lambda_(k_n)(t)U_n^*lambda_(k_n)(t)^*.
```

Prove one constant `C_D<infinity`, independent of `n` and of the external
multiplicity, such that

```text
sum_(t in T) (1-Re tau_n(V_n(t)))
 <= C_D (||sigma_n(q_19243)-1||_2 + eta_n).             (A4-DIR)
```

That single scalar inequality is the complete compiler interface.  Since

```text
2(1-Re tau_n(V_n(t)))
 = ||V_n(t)-1||_2^2
 = ||[U_n,lambda_(k_n)(t)]||_2^2,
```

`(A4-DIR)` is exactly a dimension-free bound on the minimal four-generator
conjugation Dirichlet energy of the relative chart frame.  The established
four-cycle A8 commutant gap converts it directly to chart-frame collapse.

No individual leaf trace, hub-to-leaf transport, chart alignment, matrix-valued
holonomy, or approximate A8 representation has to be recovered.

## Attempts

- **Search for one cyclic SOS identity.**  After the fixed A4 qutrit split and
  the `K_(2,2) disjoint_union K_(2,4)` tree gauge, write the left side as a
  quadratic trace functional of the four residual rectangle holonomies.  The
  desired proof can be one positive-semidefinite comparison with packet and
  collision residual energies.
- **Use a dual certificate.**  Treat `(A4-DIR)` as a finite noncommutative
  Poincare inequality.  A failed candidate PSD comparison should return a
  finite-dimensional dual vector/state showing which multiplicity mode escapes;
  feed that mode back into the packet search instead of guessing gauges.
- **Exploit the minimal generating set.**  There is no downstream benefit to
  controlling any packet letter outside `T`: `atlas-a8-four-cycle-commutant-gap`
  already turns exactly these four energies into distance from the full A8
  commutant.
- **Scalarize before synchronizing.**  Local qutrit-wire gauges may differ from
  context to context.  Because only a trace Dirichlet form is retained, average
  or pinch those gauges before attempting any operator-valued synchronization.

## Common-`U` formulation

The independent tree gauges cannot be the input to the desired inequality:
they forget the relative root gauge between the `K_(2,2)` and `K_(2,4)`
components.  Instead use the shifted products from
`atlas-a4-packet-centralizer-product-compiler` before quotienting the common
frame.  For each of the thirty constraints choose its own centralizer witnesses
`X_j,Y_j`, but retain one unitary `U` in all equations:

```text
U approximately X_j R Y_j,
X_j in U(rho(<a_j>)'),       Y_j in U(rho(<b_j>)'),
```

with the factor-reversed convention on the reversed packet words.  Define the
joint common-frame residual

```text
R_joint(U)^2
 =sum_j dist_2(U,D_j)^2+||q_19243(U)-1||_2^2,          (A4-JOINT-RES)
```

where every `D_j` is the correctly shifted product.  The exact scalar lemma
which would prove this claim is a dimension-independent comparison

```text
E_T(U):=sum_(t in T)(1-Re tau(V_U(t)))
 <= C sqrt(R_joint(U)^2),                              (A4-JOINT-DIR)
```

together with the already available conversion from packet word/stable-letter
defects to vanishing of the thirty distances.  This formulation retains
precisely the liftability datum lost by the four rectangle invariants: the same
`U` must admit all thirty factorizations.

No component-commutant expectation can prove `(A4-JOINT-DIR)`.
`atlas-a4-componentwise-commutant-collapse` is refuted, and collision
`q_19243->1` actually forces the frame squared-distance at least `1/32` from
the collision `S3` commutant.  A successful cyclic SOS must therefore compare
the scalar endpoint cocycles directly, without an intermediate assertion that
`U` is component-central.

## Exact coefficient calibration

The natural 15-point classical packet gives a lower bound on any pointwise
branch-independent constant.  Exact enumeration of the thirty inner and
thirty outer packet alignments gives, on both branches, positions with

```text
sum_(t in T) 15 ||V_U(t)-1||_2^2=96,
15 ||q_19243(U)-1||_2^2=16.                           (A4-DIR-CAL)
```

Their packet residual is zero.  Since
`E_T=(1/2)sum_t||V_U(t)-1||_2^2`, these positions have

```text
E_T=16/5,        ||q_19243(U)-1||_2=4/sqrt(15).
```

Consequently any norm-linear pointwise inequality of the form
`(A4-JOINT-DIR)` must allow

```text
C >= (16/5)/(4/sqrt(15))=sqrt(48/5).                  (A4-DIR-CMIN)
```

This does not obstruct asymptotic vanishing; it rules out importing a
constant-one contraction from conditional expectation or from the 31-point
two-holonomy coefficient `5`.

## Qualitative compactness reduction

The downstream route does not actually require the linear modulus in
`(A4-DIR)`.  It is enough that, uniformly in the multiplicity,

```text
R_joint(U_n)->0       implies       E_T(U_n)->0.       (A4-DIR-QUAL)
```

This qualitative assertion has an exact common-frame reformulation.  If it
fails, choose a sequence with `R_joint(U_n)->0` and `E_T(U_n)>=eps>0` and pass
to a tracial matrix ultraproduct.  Because there are only thirty constraints,
choose near-minimizing centralizer witnesses for each one before passing to the
ultraproduct.  Their commutation relations and all equations
`U=X_jRY_j` become exact, `q_19243(U)=1`, while `E_T(U)>=eps`.  Conversely any
such exact ultraproduct solution is represented by a sequence contradicting
`(A4-DIR-QUAL)`.  Therefore `(A4-DIR-QUAL)` is equivalent to:

> every tracial matrix-ultraproduct solution of the thirty shifted
> common-`U` factorizations and `q_19243(U)=1` has `E_T(U)=0`.

This equivalence is only a reduction, not a proof of the zero-set statement.
It sharply isolates the remaining algebra: exclude a positive four-cycle
trace state on the universal common-`U` shifted-product system, or give one
cyclic SOS separating it.  Absence of finite classical or fixed-rank `GL5`
solutions does not decide this matrix-ultraproduct zero set.

Accordingly the claim remains open.  The minimal live task is the exact
common-`U` zero-set/SOS statement above; neither independent tree gauges nor
component centrality retain enough information.
