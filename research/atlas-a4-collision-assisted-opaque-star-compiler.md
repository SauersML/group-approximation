---
rg: 2
id: atlas-a4-collision-assisted-opaque-star-compiler
kind: claim
title: Collision-assisted opaque conjugacy transports suffice for the A8 chart frame
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
 <= C_star (||sigma_n(q_19243)-1||_2 + eta_n),          (A4-STAR-1)

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

- **The entire classical simplex obeys a sharp dimension-free estimate.**
  `atlas-a4-classical-opaque-star-sharp-constant` computes all sixty exact
  packet alignments in `Reg(A8)`.  Their sharp transport coefficient is
  `1/sqrt(2)` and their sharp hub coefficient is one; the same bounds survive
  arbitrary direct sums and external amplification.  This proves that there
  is no classical-sector amplification counterexample.  It does not control
  general matrix holonomy: all sixty collision defects equal `sqrt(2)`, so
  the finite calibration contains no points approaching the required
  collision-zero fiber.

- **The collision term is forced by an exact regular spectral obstruction.**
  Packet-only opaque transport is false even on exact regular
  margins.  `atlas-a4-packet-alone-fails-opaque-star` evaluates the four
  opcodes on all sixty exact classical packet alignments, now in `Reg(A8)`
  rather than the smaller fifteen-point diagnostic.  One exact inner packet
  network with every stable letter equal to one has opcode-order profile

  ```text
  (ord V(t01),ord V(t12),ord V(t23),ord V(t30))=(4,4,2,2).
  ```

  The order-four leaves stay normalized-HS distance exactly one from the
  unitary orbit of the order-two hub, under every amplification.  Thus no
  tree-gauged packet-path telescoping estimate with right side `C eta` can
  prove `(A4-STAR-1)` on packet networks alone.  The ambient collision
  hypothesis must be used essentially.  This is why `(A4-STAR-1)` includes
  the collision residual.  The exact witness does not refute that joint
  estimate: its collision defect is nonzero.

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

- **Exact packet/collision normal closure cannot prove the hub readout
  universally.**  Put

  ```text
  Gamma=(A8*A8)/<<thirty A4 packet words,q_19243>>.
  ```

  Every displayed relator is a true word in the kernel of the canonical map
  to the binary-Leavitt target.  By `atlas-charts-overlap-trivially`, the two
  chart maps `i_1,i_2:A8->Gamma` are injective and have trivial intersection.
  In the group von Neumann algebra `L(Gamma)`, include the canonical trace in
  a finite factor `M`.  The two regular trace-preserving copies of `C[A8]` in
  `M` are unitarily conjugate (match their finite-dimensional matrix blocks),
  so some `U in M` satisfies

  ```text
  U lambda(i_1(g)) U^*=lambda(i_2(g))       (g in A8).
  ```

  This is an exact regular-margin packet/collision model: all packet errors
  and stable-letter errors vanish, and `q_19243=1`.  Nevertheless its hub
  opcode is

  ```text
  V_U(b)=lambda(i_2(b)i_1(b)^-1).
  ```

  The element is nonidentity because the chart images have trivial
  intersection.  Hence the canonical group trace gives

  ```text
  tau(V_U(b))=0,                 ||V_U(b)-1||_2^2=2.   (A4-STAR-ESCAPE)
  ```

  Thus no finite group-word normal certificate using only the exact packet
  and collision relations can imply `(A4-STAR-2)` in all finite tracial von
  Neumann algebras: its right side is zero on this model and its left side is
  `sqrt(2)`.  In particular, the fact that `b` normally generates the
  *individual* simple chart `A8` does not control the cross-chart relative
  cocycle.  The cocycle is not a representation, and true kernel relators
  cannot algebraically identify the two faithful chart factors.

  This does not refute the stated matrix-only claim: the quotient trace need
  not be Connes embeddable.  It proves that the least-attempted direct route
  cannot close by an ordinary finite normal-closure/telescoping certificate.
  Any proof of `(A4-STAR-2)` must be a genuinely finite-dimensional trace
  obstruction excluding `(A4-STAR-ESCAPE)` from matrix ultraproducts (which
  is precisely the packet-collision quotient fork), while `(A4-STAR-1)` still
  separately requires collision-assisted relative-cocycle equivariance.  The
  exact certificates can only propagate a hub estimate after those analytic
  inputs are supplied.

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
  `O(eta_n+||sigma_n(q_19243)-1||_2)`.
- **Collision readout separately.**  Track `q_19243` only far enough to prove
  `(A4-STAR-2)`.  The three transport proofs need not reconstruct the collision
  word or any A8 multiplication state.
- **Finite search objective.**  Minimize the number of distinct packet
  rectangle/stable-letter residuals touched by the three paths.  The abstract
  four-transvection generator theorem proves there is no reason to optimize a
  larger star.
- **Collision has one exact continuous blind sector.**
  `atlas-19243-has-continuous-regular-s3-line-holonomy` rewrites the relative
  collision group with `x=cs` as
  `sxs=x^(-1), r x^2 r=x r x` and exhibits its infinite-dihedral quotient.
  More decisively, it constructs a continuous six-dimensional family with
  restriction exactly `Reg(S3)` and with a balanced collision involution:
  an arbitrary dihedral reflection angle on `triv direct_sum sign`, balanced
  by `c=+1` and `c=-1` on the two standard copies.  Therefore collision does
  not reduce to finitely many local representation types and cannot by itself
  control the multiplicity holonomy.  The minimal positive estimate must use
  common-`U` packet coupling to transfer control from the standard blocks into
  this line sector.
