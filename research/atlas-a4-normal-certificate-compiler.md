---
rg: 2
id: atlas-a4-normal-certificate-compiler
kind: claim
title: Three opaque conjugacy transports and the 19243 readout suffice for the A8 chart frame
distinct_from:
  atlas-a4-full-packet-normal-generator-table-compiler: that stronger target constructs a 20160-state approximate multiplication table; this target asks only for three pairwise conjugacy transports around the collision opcode.
  atlas-a4-full-packet-normal-generator-holonomy-compiler: that stronger target rounds residual holonomy to an exact A8 representation; this target never constructs even an approximate representation.
artifacts:
  - experiments/atlas_a8_minimal_transvection_cycle.py
  - experiments/atlas_a4_19243_normal_closure.py
---

Use the minimal directed-cycle transvection set

```text
T={t01,t12,t23,t30} subset GL_4(F2)=A8,
```

with collision translation `b=t23`.  By
`atlas-a8-minimal-four-transvection-cycle`, these four transvections generate
all of `A8`, every other member of `T` is conjugate to `t23`, and no three
transvections can generate the full chart.  Thus a collision-centered
transvection star cannot have fewer than three leaves.

For a normalized exact-regular A4 context network `sigma_n,U_n,eta_n`, define
the four opcodes directly from the relative chart frame:

```text
V_n(t)=U_n lambda_(k_n)(t) U_n^* lambda_(k_n)(t)^*.    (A4-STAR-0)
```

Construct only three auxiliary unitaries

```text
A_n(t),       t in {t01,t12,t30},
```

and constants `C_star,C_col<infinity`, independent of `n`, such that

```text
max_(t in {t01,t12,t30})
 ||V_n(t)-A_n(t)V_n(t23)A_n(t)^*||_2
 <= C_star eta_n,                                       (A4-STAR-1)

||V_n(t23)-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2 + eta_n).           (A4-STAR-2)
```

That is the whole compiler interface.  The three transports are deliberately
**opaque**: they need not represent the frozen A8 conjugator words, satisfy any
multiplication law, agree with one another, or be close to canonical chart
matrices.  `unitary-star-conjugacy-hs-collapse` propagates the collision
smallness to all four raw covariance opcodes, and
`atlas-a8-four-cycle-commutant-gap` then supplies the global regular-chart
decoder automatically.

The exact finite audit has therefore optimized the incidence pattern as far as
a transvection-only star can possibly go: one hub plus three leaves.  The price
of this minimum is that `t30` is a derived full-chart opcode rather than one of
the six adjacent chain generators.  Analytically this is acceptable because
`V_n(t30)` is defined directly by the exact chart representation; the packet
only has to transport its covariance block.

## Attempts

- **Exact chart conjugacy does not transport relative opcodes.**  The
  established A8 normal certificates alone cannot prove `(A4-STAR-1)`.  Let
  `G=A8`, let `lambda` be its left regular representation, fix two distinct
  transvections `b,t`, and let `U` be the diagonal sign which is `-1` on the
  two-element subgroup `<b>` and `+1` off `<b>`.  Left multiplication by `b`
  preserves `<b>`, so

  ```text
  V_U(b)=U lambda(b) U^* lambda(b)^*=1.
  ```

  Since `t` is not in `<b>`, the sets `<b>` and `t<b>` are disjoint.  Thus
  `V_U(t)` is diagonal with value `-1` on their four-point symmetric
  difference and `+1` elsewhere, giving

  ```text
  ||V_U(t)-1||_2^2=16/|A8|=1/1260.
  ```

  Although `t` and `b` are conjugate in `A8`, no unitary can conjugate
  `V_U(b)=1` to this nonidentity `V_U(t)`.  Hence
  `atlas-a8-minimal-four-transvection-cycle` and
  `atlas-a8-six-transvection-normal-certificates` supply only the endpoint
  group identities.  The minimal genuinely missing sublemma is an A4 packet
  **relative-cocycle equivariance** estimate: the tree-gauged packet paths
  must control the change from `U` to `lambda(a)^*U lambda(a)` strongly enough
  to transport `V_U(b)` to each leaf opcode.  This is additional analytic
  content and cannot be replaced by the frozen A8 conjugator words.

- **Existing 19243 readouts do not give the amplified hub estimate.**
  `atlas-a4-gl5-two-holonomy-readout` proves a sharp inequality only on the
  202 exact positions in one fixed 31-point permutation model and explicitly
  does not cover arbitrary matrix-valued Schur holonomy.  The exact identity
  `atlas-word-19243-is-kernel-relation` likewise supplies no normalized-HS
  estimate for `V_n(t23)`.  Thus `(A4-STAR-2)` remains a separate amplified
  collision-to-cocycle readout; none of the established exact packet lemmas
  currently discharges it.

- **Search three transports, not a group law.**  In the canonical
  qutrit/multiplicity splitting, seek packet paths carrying the `t23` covariance
  block to `t01`, `t12`, and the transverse `t30` covariance block.  Only the
  endpoint conjugacy inequality matters.
- **Make `t30` the unique transverse leaf.**  The affine/rank-three packet core
  already sees `t01,t12,t23`-type directions.  Concentrate the central-`C3`
  escape machinery on the single star edge ending at `t30`; this is where the
  proof must leave the parabolic.
- **Tree-gauge first.**  After the `K_(2,2) disjoint_union K_(2,4)` gauge there
  are four rectangle holonomies.  Search for three bounded paths in this
  four-holonomy network whose endpoint conjugacy errors telescope to
  `O(eta_n)`.
- **Collision readout separately.**  Track `q_19243` only far enough to prove
  `(A4-STAR-2)`.  The three transport proofs need not reconstruct the collision
  word or any A8 multiplication state.
- **Finite search objective.**  Minimize the number of distinct packet
  rectangle/stable-letter residuals touched by the three paths.  The abstract
  four-transvection generator theorem proves there is no reason to optimize a
  larger star.
