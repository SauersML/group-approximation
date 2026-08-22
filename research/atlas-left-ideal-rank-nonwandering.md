---
rg: 2
id: atlas-left-ideal-rank-nonwandering
kind: claim
title: The augmented left relator ideal cannot wander across repeated natural chart modules
distinct_from:
  atlas-defect-orbit-span-quotient-dichotomy: that gives an exact quotient when the relator orbit-span is proper; this is the missing normalized-rank theorem asserting properness for low-rank augmented residuals.
  atlas-augmented-relator-ideal-not-left-finite: that rules out a universal finite algebraic spanning list; this asks for a representation-specific Sylvester-rank estimate despite the infinite one-sided generating width.
  atlas-augmented-rank-zero-set-compactness: that states the finite-zero promotion conclusion; this is its precise finitely presented module input.
  atlas-morita-coefficient-cyclicity-reduction: that exactly identifies the full orbit-span with a coefficient-algebra cyclic span on the multiplicity space; the present claim is the still-missing assertion that the fourteen literal residual formulas cannot create a sublinear cyclic seed.
---

OPEN.  Use the notation

```text
P=F2[A8*A8],
I=ker(P -> F2[Gamma_+]).
```

For every finite-dimensional left `P`-module `E` whose restriction to each
`A8` factor is the same repeated natural module `V^m`, let

```text
D_E=sum_(r in R_+) im(r-1),
I E=sum_(a in P) a D_E.                               (LRN1)
```

Prove the representation-specific nonwandering implication

```text
max_(r in R_+) rank_E(r-1)/dim(E) ->0
       implies
dim(I E)/dim(E) ->0                                   (LRN2)
```

for every sequence of such modules.  The weaker conclusion
`liminf dim(IE)/dim(E)<1` is already sufficient to extract one exact finite
quotient.

This is the surviving Sylvester-rank module statement.  It cannot follow
from finite one-sided generation: `atlas-augmented-relator-ideal-not-left-finite`
proves that `I` has infinite left generating width.  Nor can it be tested by
one fixed formal symbol: the cyclic and formal-Toeplitz promotion theorems
already close those cases.  A proof must instead find a rank inequality or
shrunk-subspace certificate special to the thirteen relations and the two
`V^m` restrictions, controlling all moving left translates at once.

An explicit countermodel would be equally decisive: construct modules
`E_n` of this marked type with `dim D_(E_n)=o(dim E_n)` but

```text
I E_n=E_n.                                             (LRN3)
```

By the fixed-width fences, such a construction must have growing state width
or genuinely nonstationary coefficient data.

## Attempts

- **Finite one-sided saturation fails algebraically.**  If finitely many
  left translates of the thirteen generators spanned `I`, their images would
  give `(LRN2)` by rank subadditivity.  The established non-left-finiteness
  theorem rules out exactly this argument.
- **Fixed symbolic finite sections specialize.**  Block-circulant,
  low-rank cyclic perturbation, and fixed formal-Toeplitz gauges all promote
  to exact finite-field points.  They cannot supply `(LRN3)`.
- **Generic cyclicity is irrelevant.**  Two conjugate matrix-algebra chart
  actions can make a rank-one subspace cyclic, but this does not arrange that
  the cyclic seed is the simultaneous image of the thirteen specific
  relator residuals.  A generic expansion argument therefore neither proves
  nor refutes `(LRN2)`.
- **Universal ideal identities are too strong.**  A fixed identity placing a
  nonzero chart marker in the two-sided relator ideal would also hold in the
  exact binary-Leavitt image, where both chart copies remain faithful.
  Any positive certificate must use finite-module rank selection rather than
  ordinary ideal membership.
- **Bass--Serre Folner compression has the wrong modular chart type.**
  `atlas-edge-folner-modules-miss-natural-type` compares one transvection:
  its normalized `rank(t-I)` is `1/2` on every free/regular edge-orbit module
  but `1/4` on `V^m`.  A vanishing-density boundary cannot pay this fixed
  gap.  Thus truncating the infinite chart-coset graph does not construct
  `(LRN3)`; a negative model needs positive-density nonfree chart cells and
  a new mechanism keeping all fourteen literal residual images small there.
- **Morita reduction isolates the exact growing-width enemy.**
  `atlas-morita-coefficient-cyclicity-reduction` writes the chart change as
  a `4 by 4` block matrix `T=(T_ia)` with inverse `(S_bj)`.  The full defect
  orbit is exactly `V tensor C_T U_D`, where
  `C_T=<T_ia S_bj><=M_m(F2)` and `U_D` is the multiplicity-coordinate span
  of the fourteen literal residual images.  Thus a countermodel is precisely a
  sequence in which `dim U_D=o(m)` but `C_T U_D=F2^m`.  This also proves
  that its alternating saturation depth is at least
  `log_16(1/(14 epsilon))` when every normalized residual rank is at most
  `epsilon`.  Generic coefficient algebras can have one-dimensional cyclic
  seeds.  In fact the cited reduction gives an explicit binary unipotent
  chart change whose coefficient algebra is `M_m(F2)`, so the
  repeated-natural chart type alone cannot close the claim;
  the remaining input must use the fourteen explicit residual formulas to
  force a proper `C_T`-invariant subspace.

- **The literal and carrier residual counts differ.**
  `atlas-literal-augmented-residual-count-is-fourteen` records that the
  two-chart presentation used here has twelve packet cubes, q14, and
  collision.  The familiar count thirteen applies only after q14 is absorbed
  exactly into the virtually-free carrier.  Since `(LRN1)` starts from an
  arbitrary `A8*A8` module, its rank sum has fourteen terms.

- **q14 has a linear rank correction, but not yet a chart correction.**
  `atlas-q14-rank-centralizer-projection` writes the two marked
  transvections as `1+N,1+M`.  The q14 residual rank is exactly
  `rank(NM-MN)`, and changing at most four times that rank replaces `M` by
  an element of the centralizer of `N`; its remaining square-zero defect is
  at most eight times the q14 defect.  This does not preserve the Jordan
  type of `M` or extend the corrected involution to the full second `A8`
  chart.  Hence passing rigorously to the thirteen-filling carrier requires
  a relative `V4` rank-correction theorem, not merely the linear commutator
  projection.

- **The relative q14 chart correction is available flexibly.**
  `atlas-q14-relative-chart-rank-correction` applies rank stability of the
  four-dimensional algebra `F2[r,s]/(r^2,s^2,rs-sr)`, tunes the two
  marginal Jordan ranks using `o(m)` auxiliary blocks, and uses
  `square-zero-near-conjugacy-in-rank` to conjugate the two full `A8` charts
  nearby.  Thus q14 may be made exact without losing any vanishing-rank
  packet or collision residual.  The relation-specific endpoint can
  legitimately be studied as the thirteen post-q14 residuals: twelve packet
  cubes plus collision.  No analogous correction of those fillings follows
  from the finite-algebra theorem.

- **Exact q14 supplies no coefficient invariant.**
  `atlas-q14-exact-allows-full-coefficient-cyclicity` constructs binary
  chart changes inside the marked transvection centralizer for which q14 is
  exact but `C_T=M_m(F2)`.  Thus even after the flexible q14 correction a
  one-dimensional arbitrary seed can wander through the whole carrier.  A
  conserved multiplicity subspace must use the twelve packet formulas and
  collision jointly; q14 and chart type contribute none by themselves.

- **Packet plus collision also permits a full coefficient algebra at
  multiplicity two.**
  `atlas-packet-collision-m2-has-full-coefficient-algebra` evaluates the
  stored exact packet-and-19243 escape and finds four coefficient products
  equal to the four matrix units of `M_2(F2)`.  Thus neither the twelve cubes
  nor collision blocks coefficient cyclicity on that exact stratum; q14 is
  the first relation rejecting it.  Direct amplification does not refute
  nonwandering, because `M_2 tensor I_k` needs a seed of dimension at least
  `ceil(k/2)`, density at least `1/4`.  A genuine enemy must combine q14 with nonstationary
  cross-amplification mixing, not repeat the known two-copy escape.

- **Approximate coefficient substitution retains the q14 wall.**
  `atlas-m2-coefficient-substitution-cannot-dilute-q14` treats the natural
  attempt to replace the four `M_2(F2)` matrix units of the exact escape by
  growing shift/wrap matrices.  If their multiplication table has vanishing
  normalized-rank defect, finite-algebra rank stability corrects it to a
  standard amplification, and the rank-one q14 defect retains normalized
  rank `1/8-o(1)`.  Thus an enemy must deliberately violate coefficient
  multiplication on moving low-rank directions and use the thirteen Atlas
  word formulas to cancel those violations; a functorial coefficient
  amplification cannot work.

- **Low-rank bridges out of a fixed-width phase cannot become cyclic.**
  `atlas-fixed-width-phases-resist-low-rank-bridging` treats the proposed
  perturbation of a direct amplification of the exact multiplicity-two
  phase.  If the whole chart change moves by rank `r`, each of its `4^4`
  coefficient generators moves by rank at most `2r`.  All coefficient words
  applied to a seed `U` remain in the tensor product of the fixed-width
  factor with the passive-coordinate span of `U` and those finitely many
  error images.  Quantitatively, for width `s`,
  `dim(C_TU)<=s^2(dim U+512r)`.  Thus an `o(k)` seed plus an `o(k)` bridge
  cannot fill a `sk`-dimensional multiplicity space.  Rank-one outer-product
  bridging, even though it changes every fixed residual by only bounded
  rank, cannot supply `(LRN3)`.  A countermodel must move linearly far from
  every fixed-width amplified coefficient phase, not merely connect its
  multiplicity copies on a low-rank set.

- **The width dependence is sharp already on the q14 locus.**
  `atlas-q14-growing-width-rank-one-bridge-is-sharp` takes a multiplicity
  space `M=F2^s tensor F2^k` with `k<=s`.  Two shift/wrap blocks generate
  `M_s tensor I_k`, and one rank-one outer-product block has `s` left and
  right multiplicity coordinates spanning `F2^k` and its dual.  Sandwiching
  that block by `M_s` generates all of `M_(sk)`.  The three chart positions
  are pairwise square-zero and lie in the marked-transvection centralizer,
  so the chart is invertible and q14 is exact.  At `s=k=sqrt(m)`, a rank-one
  bridge therefore makes a one-dimensional seed cyclic.  Together with the
  preceding bound, this pins the transition at square-root phase width up
  to constants.  The construction does not control the twelve packet cubes
  or collision: any compactness proof must use those thirteen formulas to
  rule out precisely these growing-width outer-product frames; q14 and
  abstract coefficient cyclicity cannot do so.

- **On the square-root frame the remaining problem is an explicit
  two-matrix rank system.**
  `atlas-square-root-bridge-two-matrix-rank-reduction` defines, for each of
  the twelve packet cubes and collision, a fixed polynomial
  `P_w(X,Y)` by evaluating the unipotent chart
  `I+E13 tensor X+E14 tensor Y`.  After amplification by `I_k`, its residual
  rank is exactly `k rank P_w`.  Adding the cyclic rank-one `E24` bridge
  changes the rank of word `w` by at most twice its number of second-chart
  syllables.  Consequently, generating pairs `X_s,Y_s in M_s(F2)` with all
  thirteen `rank P_w=o(s)` compile at `k=s` to q14-exact, full-coefficient
  microstates on dimension `4s^2`.  If one bridged residual remains nonzero,
  its image is cyclic and gives `(LRN3)`.  The surviving positive target is
  therefore a rank-density theorem for these thirteen explicit two-matrix
  polynomials, modulo exact augmented zeros; this is the first place the
  packet and collision formulas enter the growing-width sector.

- **Collision has no constant-term density wall on the square-root frame.**
  `atlas-square-root-collision-constant-term-is-zero` corrects the tempting
  contrary inference.  At `X=Y=0`, the four second-chart collision letters
  lie in one `S3`, multiply to one, and commute with the repeated
  first-chart involution, so collision is exactly one.  Identity fails the
  packet, not collision.  Hence the previously recorded claim that
  collision-small forces `rank[X Y]/s>=1/8` is refuted.  Any positive rank
  inequality must combine at least one packet polynomial with collision;
  collision alone supplies no density floor in these coordinates.

- **The combined positive-density target is a concrete stably-finite
  quotient test.**
  `atlas-two-matrix-bezout-rank-gap-criterion` forms
  `B=F2<x,y>/<entries of the thirteen P_w>`.  A finite identity
  `1=sum a_j p_j b_j` immediately gives
  `s<=sum_j rank p_j(X,Y)` and hence a uniform normalized-rank gap; no
  coefficient-norm estimate is needed.  Conversely, any sequence making all
  thirteen polynomial ranks `o(s)` yields a unital homomorphism from `B` to a
  stably finite rank-metric matrix ultraproduct.  Thus a symbolic audit should
  seek either an ordinary Bezout certificate or, more generally, prove that
  `B` has no nonzero stably finite unital quotient.  Merely proving `B`
  nonzero does not construct a countermodel, and the full-generation face
  cannot be encoded by one fixed polynomial because its Burnside witness
  length grows with `s`.

- **The q14 triangular square-root frame is killed by one packet edge.**
  `atlas-square-root-frame-has-unit-packet-residual` uses the explicit
  `H18=S3 x C3` labels.  In the q14-adapted basis, one packet involution is
  `b=I+E14`; an adjacent order-three label acts on the disjoint plane, so
  `(ba)^3=b`.  The entire triangular frame, including its cyclic `E24`
  rank-one bridge, commutes with `b`.  Therefore either orientation of this
  packet edge evaluates to the same fixed residual `b-I`, of multiplicity
  rank exactly `s`.  One scalar residual entry is the constant polynomial
  `1`, so the two-matrix quotient `B` is zero with a length-one Bezout
  certificate.  This decisively closes the square-root outer-product family:
  a surviving growing-width enemy must leave this q14 triangular centralizer
  slice, not merely choose more complicated positive-density `X,Y` inside it.
