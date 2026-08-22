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

- **The minimal forward-collision support is one explicit one-relator
  quotient.**  `atlas-forward-collision-bass-serre-reduction`
  identifies the pre-collision carrier as

  ```text
  G0=(C3 x S3) *_(C3^2) (C2^4 : C3^2) *_C2 S3
  ```

  and shows that all three regular vertex margins glue at every atlas
  multiplicity.  Collision is a cyclically reduced length-six hyperbolic word
  `t|c|s|c|t^-1|cbc`, not a translation in `C2^4`; hence a translation-normal-
  closure shortcut cannot prove the hub estimate.  The exact remaining seam
  is whether the three finite vertex groups inject in a finite quotient after
  adjoining that relator, or whether the common involution dies.  The repeated
  `c` also rules out strict relative `C'(1/6)`, so no vertex injection is being
  smuggled in through a borderline small-cancellation claim.

- **That one-relator quotient has faithful finite vertex images.**
  `atlas-forward-collision-has-faithful-s288-amalgam` gives a structural
  degree-288 construction, and
  `atlas-forward-collision-has-faithful-a10-quotient` independently gives
  five explicit degree-ten permutations generating `A10`.  In the latter
  image the vertex subgroup orders are exactly `18,144,6`, and
  `Reg(A10)` realizes the compatible atlas margins at multiplicity `90`.
  Hence neither collision nor one forward edge kills the common involution,
  even after the minimal internal chart supports are included.  The next
  obstruction must use at least one of the remaining rank-three core edges.

- **The A10 point carrier stops at the very next core edge, even after
  padding.**  `atlas-a10-natural-padding-fails-next-core-edge` computes the
  twelve canonical first-chart extensions inside the natural `A10`; all have
  large-core mask `0x1`.  More generally no involution completing the missing
  `S3 x S3` support and the next A4 edge exists in the natural `S_d` padding
  for any `d>=10`.  The all-`d` statement follows from the fixed-orbit split,
  not from a bounded extrapolation.  This locates the first failed point-model
  edge, while leaving its regular-representation triangle completion open.

- **That A10 triangle completion collapses universally.**
  `atlas-a10-first-core-cycle-collapses` computes the preceding small
  triangle colimit exactly.  It is only `S3`: the generators `r,t,u` die, so
  the `J` vertex of order `288` and the new `A4` vertex cannot inject.  This
  upgrades the natural-padding screen to a no-overgroup theorem for the A10
  carrier.  The qualifier remains load-bearing: other faithful finite images
  of the minimal forward-collision quotient need not have the same
  `J=<F,t>` relations, so a global matrix obstruction still has to control
  all carrier types.

- **Changing carrier type reaches a third large-component edge.**
  `atlas-a8-carrier-reaches-third-large-core-edge` gives an exact degree-eight
  `A8` image satisfying the minimal forward-collision support and the first
  three of the four large `K2,2` pair-cubes.  Its regular representation is
  already at atlas multiplicity one.  Thus neither the A10 collapse nor the
  first cycle is a global obstruction.  The same bounded low-index census has
  masks only `0x3,0x7,0xb`, never all four, so the fourth edge is now the first
  unresolved relation in this carrier ladder.

- **All four large-component edges complete locally in A5.**
  `atlas-large-k22-has-faithful-a5-completion` gives a five-point image in
  which both `S3` vertices and all four `A4` edges inject.  At regular atlas
  multiplicity one, `336 Reg(A5)` has exactly the required `S3` and `A4`
  restrictions.  The missing fourth edge is therefore not intrinsically
  obstructed: the global seam is compatibility of the marked
  `A5=<r,y,b>` with the collision/forward carrier, where the fourth first-side
  involution is recovered as `u=r^-1 b y^-1`.

- **The other component supplies a moving regular-A4 carrier.**
  `atlas-collision-involution-is-an-a4-bridge-to-h6` proves the exact
  asymmetric incidence

  ```text
  [b_0,K]=1,                 <C_6,b_0> ~= A4.
  ```

  Hence for the literal common frame `U`, the collision involution
  `c(U)=U^*rho(b_0)U` comes with a canonical transported line carrier
  `P_6(U)=U^*P_6U`; the regular-A4 `1` versus `1/3` compression gap applies
  to that pair with constant `2/3` at every multiplicity.  The remaining
  packet step is now precise: use the `H_6` rectangle equations to replace
  the moving `P_6(U)` by the fixed `P_6` on
  `E_K^-c(U)E_K^+`.  Ambient subgroup identities alone do not make this
  replacement, so the result is a common-`U` reduction rather than a
  collision-only hub proof.

  The same exact closure is stronger: `<H_6,b_0> ~= S4`, this `S4` meets the
  rank-three core exactly in `H_6`, and it meets `K` trivially.  Thus the
  finite operator problem behind the replacement is the branching
  `Reg(S4) downarrow H_6`, coupled through the literal common `U` to the
  disjoint `K` line.  A calculation internal to either factor separately
  cannot perform that coupling.

- **Even the full regular local collision cell has a common-`U` hub escape.**
  `atlas-19243-common-u-regular-local-hub-gram-escape` works on the literal
  `Reg(K x L)` cell, fixes the actual involution `b`, and rotates its
  positive/negative eigenspaces only in the `K` trivial/sign carrier.  It has

  ```text
  q_19243=1,
  Re tau(V_b)=(2+cos(2 theta))/3,
  tau(V_b^2)=(2+cos(4 theta))/3.
  ```

  Hence neither the hub energy nor its canonical projection-Gram coordinate
  is controlled by collision, even with a single common `U` and exact regular
  `S3 x S3` local margins.  The missing mixed moment must use the other
  `H_6` packet component.  This rules out every proposed identity internal to
  the collision cell before any four-rectangle calculation is attempted.

- **Second moments have a canonical common-`U` coordinate, but rectangles do
  not.**  `atlas-common-u-second-moment-is-one-projection-gram` gives the
  exact identity

  ```text
  tau(V_t^2)=1-16[tau(P_tQ_t)-tau(P_tQ_tP_tQ_t)],
  Q_t=U P_t U^*.
  ```

  This is the smallest root-gauge-independent scalar which detects the
  order-two/order-four mismatch in the finite screen.  In contrast,
  `atlas-shifted-factorizations-have-independent-right-gauge` shows that the
  thirty local factorizations of one `U` carry independent
  `rho(A8)'`-gauge fibers.  Hence the four rectangles extracted from chosen
  edge messages are not canonical functions of `U`.  Any rectangle-to-Gram
  proof must first fix or quotient these gauges, or supply one additional
  mixed moment selecting a common section.

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
- **The finite connection coefficient for that transfer is positive and
  exact.**  `atlas-a4-two-c3-line-carriers-have-exact-angle-gap` computes the
  full principal-angle spectrum between the two packet `C3`-fixed spaces in
  `Reg(GL3(2))`.  Off the common constant line the squared cosine is at most
  `1/2+sqrt(17)/18`.  Hence the line-sector escape pays
  `(9-sqrt(17))/18` as soon as the common-`U` equations expose the same defect
  vector to both components.  What remains is precisely that compression
  identity; separate rectangle gauges cannot supply it.
- **Gauge-free form of the last identity.**  The collision angle is the
  canonical off-diagonal block
  `Z(U)=E_K^- U^*rho(b_0)U E_K^+`.  Vectorization puts it in the tensor-square
  `K` line carrier, where the same exact connection gap holds.  It is enough
  to prove that the fourteen common-`U` shifted packet residuals control
  `||Z(U)-P_6Z(U)P_6||_2`; the independent factorization witnesses never
  appear.  This is the smallest symbolic equation still missing before the
  continuous collision sector can be removed.
- **Closed rectangle holonomies cannot replace that mixed compression.**
  `atlas-four-rectangles-do-not-descend-to-common-u` classifies the four
  degree-four cycles of `K_(2,2) disjoint_union K_(2,4)`.  On the canonical
  common-product lift every edge equals `U`, so all four cycles are exactly
  flat; on factor-level lifts their spectra vary with the independent
  right-regular gauges.  Collision therefore cannot force a useful cycle
  invariant.  The gauge-free `Z(U)` compression above is not optional: it is
  the first remaining coordinate that actually lives on the common-frame
  quotient.
- **The omitted central sector has a directed finite asymmetry.**
  `atlas-central-c3-directed-gl5-classification` splits its sixteen word
  occurrences into two directed `K_(2,2)` blocks.  Among all 216 exact GL5
  points satisfying the fourteen-word core and `q_19243=1`, none satisfies
  even one constraint with the central label in chart one.  But 94 satisfy
  all four distinct reverse constraints, yielding an exact common-frame model
  satisfying 22 of the 30 packet words while every rank-three covariance
  generator still moves.  Thus an opaque-star proof cannot invoke an
  undirected slogan that the packet merely sees the central `C3`.  Its first
  indispensable input is the forward directed central block; the reverse
  block plus the full rank-three core remains insufficient.
- **A single forward representative already empties the standard GL6
  fiber.**  `atlas-one-forward-c3-has-no-standard-gl6-completion` performs an
  exact Boolean classification of every relative `R in GL_6(F2)` between
  standard `A8` charts with two trivial padding coordinates.  The fourteen
  core equations, collision, and one fixed forward central triangle are
  inconsistent.  Together with
  `a4-triangle-propagates-inverse-c3-edge`, one triangle also supplies its
  inverse-`C3` partner.  This is strong finite-module evidence for the
  forward block, but it is not yet the required arbitrary-multiplicity
  complex HS estimate.
- **One forward fan and its adjacent core fan have an exact 144-state escape.**
  `atlas-shared-forward-fan-is-2four-by-3two` identifies their universal
  completion as `C2^4 semidirect C3^2`.  Because `20160=140*144`, amplified
  regular representations of this group match the regular A8 cyclic margins
  and both regular A4 context margins at every external multiplicity, while
  the common relative frame remains noncentral.  Thus the forward edge cannot
  pay any positive Gram energy through its shared involution locally.  A
  valid matrix-only estimate must use collision and at least one additional
  core edge which leaves this two-fan carrier.
- **The mixed compression descends, but collision leaves a zero interval.**
  `atlas-mixed-c3-gram-has-local-zero-interval` expresses the leakage directly
  through any product `U=X_eRY_e`, proving invariance under all twelve edge
  gauges.  On the exact regular local collision family it equals
  `sin(2theta)^2 Lambda_*`, with
  `((9-sqrt(17))/108)<=Lambda_*<=1/6`.  Thus collision and all local profile
  data allow a full interval starting at zero.  The sole remaining content is
  whether the other component's simultaneous double-coset equations force
  the endpoint `Lambda=0`; no local spectral strengthening can do so.
- **Regular symmetry does not promote the repeated collision slice.**
  `atlas-collision-fiber-has-no-block-symmetrization` shows
  that the `K`-multiplicity unitary group fails to preserve the packet
  coefficients, while the actual scalar symmetry averages every collision
  orbit to zero.  The packet energy is explicitly nonconvex (`R` and `-R`
  have zero energy but their midpoint has energy 30), so conditional
  expectation plus polar repair supplies no minimizer reduction.  Thus the
  exact two-`3 x 3` Procrustes calculation remains a restricted search slice,
  not an all-fiber theorem.
- **q14 adds a wall, not a gauge fixing.**
  `atlas-q14-adds-stratified-thirteenth-double-coset` writes the actual
  packet-plus-19243-plus-q14 system as the twelve common products together
  with one finite union of involution double cosets indexed by an intersection
  dimension `m`.  All twelve right-regular witness gauges survive unchanged.
  The gain is the sharp common-`U` coordinate
  `x_30^2>=1/2` at q14 defect zero.  The quotient finite-factor escape also
  survives after q14 is added, so the required opposing strict upper bound
  remains genuinely matrix/CE-sensitive rather than an algebraic normal-form
  consequence.
