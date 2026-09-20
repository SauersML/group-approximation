---
rg: 2
id: leavitt-nonhyperlinear-from-kazhdan-heat-rounding
kind: route
title: Round global Kazhdan heat to select a scalar commutant and native heat to contradict it
target: binary-leavitt-unit-group-is-not-hyperlinear
requires:
  - kazhdan-heat-maps-round-to-finite-algebras
  - property-t-laplacian-sos-certificate
  - elementary-groups-over-fg-rings-have-property-t
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
  - research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md
  - research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md
  - research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md
  - research/artifacts/leavitt-heat-rounding-forces-unbounded-trace-distortion-2026-09-08.md
  - research/artifacts/leavitt-regular-trace-cp-reversal-2026-09-08.md
---

Put R=L_(F_2)(1,2). Prefix-code matrix self-similarity and GL=EL identify
H=R^x with EL_4(R) and its native rank-three corner L with H. Both are
finitely generated Kazhdan. Infinite simplicity makes H ICC.

Suppose H is hyperlinear and choose full canonical H-microstates. Fix a
finite inverse-paired generating list and an SOS certificate. The heat
rounding prerequisite applies at admissible times. Section 2 of the
two-use artifact gives the following selection, whose details were
rechecked in Sections 2-3 of the September 20 audit.

1. Uniform global heat rounding to E_(B_n) permits Haar averaging and polar
   completion of the generators into B_n', at error gamma_n->0. These are
   still full canonical microstates, not genuine representations.
2. Slow the heat to tau_n->infinity so that tau_n gamma_n->0 and
   `tau_n^2 sum_(r in J_n)||W_(n,r)-I||_2^2 ->0` for increasing relation
   prefixes containing the SOS rows. The corrected heat still rounds to
   E_(B_n).
3. Decompose B_n as direct sums of M_(a_i) tensor I_(b_i). Component
   scalar-heat errors and relation defects average with physical trace
   weights a_i b_i/d_n. ICC conjugate averaging gives, for each g!=1,
   `sum_i (a_i b_i/d_n)|tr_(b_i)(W_(n,i,g))|^2 ->0`.
4. Select a component with combined heat, time-weighted relation, and
   growing-prefix trace cost at most the mean. Its tuples are canonical,
   their heat tends uniformly to scalar expectation, and their selected
   SOS defects still satisfy epsilon_n tau_n->0. Integrated heat retention
   fixes every bounded asymptotic commutant sequence. Consequently the full
   external H-commutant in the selected matrix ultraproduct is C1.

Now restrict the selected model to L, or precompose with H isomorphic to L.
It is again a full canonical model. Choose times slowly enough for the
transported SOS rows and fixed native compressor rows. The universal heat
rounding claim applies a second time in these selected dimensions.

Let u be the native compressor, K the fourth-coordinate R^x, and
D=pi(L)' cap M. For native heat P and Q=Ad(U)P Ad(U*), the compressor
identity uLu^-1<=L gives `||QP-P||_(infinity->2)->0`. The native element
k=diag(I_3,1+et) in K has y=uku^-1=x_12(e) in L, nonidentity. Canonicality
and factoriality of pi(L)'' imply E_D(pi(y))=0, whereas Q fixes its class.
Thus `||PQ-Q||_(infinity->2)->1`.

Transfer these defects through rounding P to E_(A_n). The finite balanced-
flow central-height lemma produces z_n in Z(A_n), with trace zero,
operator norm at most one, L2 norm at least 1/8, and [U_n,z_n]->0.
Uniform heat identification gives D=[A_n]_omega, hence z in Z(D)
commuting with pi(u). Since pi(K)<=D, z commutes with pi(uKu^-1).

The native identity H=<L,uKu^-1> is proved directly by Leavitt and
Steinberg relations in Section 3 of the central-height artifact. Explicitly,
uKu^-1 contains x_14(ar) and x_41(rb), with ba=1, so
`[x_21(b),x_14(ar)]=x_24(r)` and
`[x_41(rb),x_12(a)]=x_42(r)`; L supplies the other roots.
It follows that z belongs to the global H-commutant and is central there.
Its positive L2 norm and zero trace contradict the selected scalar
commutant. Therefore H is not hyperlinear.

This route uses the narrower sequential heat theorem proved in the cited
two-use artifact. It does not apply modus ponens to the broader
title-level statement `leavitt-channel-rounding-forces-nonhyperlinearity`
without its unrestricted channel premise. All unresolved analytic content
remains visible through the heat-rounding prerequisite.

**Attribution.** The proposed internality input behind the heat premise is
Jihao Liu, [*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7; Proposition 3.1 records the compatible uniform
expectation-lift criterion. This Leavitt deduction is Cairn's conditional
application of Liu's analytic theorem, not a theorem claimed in the paper.
Component selection and the native central-height endgame are the separate
September 8 Cairn two-use argument in the cited artifacts. The September 20
audit checks their interface with Liu's theorem without certifying its
upstream proof.
