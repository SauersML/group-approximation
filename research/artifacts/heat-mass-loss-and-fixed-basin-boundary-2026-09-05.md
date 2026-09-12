# Heat mass loss and the boundary of a fixed HS basin

The curved Hodge theorem improves supplied low-energy mass. It cannot
in general retain all that mass up to O(delta^2). Moreover, full flexible
correction throughout a fixed normalized-HS neighborhood of exact
representations would already imply global flexible stability. These
are precise limitations on two possible upgrades of the heat argument.

## 1. A small fixed fraction of mass can be irretrievably mismatched

Take G=SL_5(Z) and a nontrivial k-dimensional irreducible unitary
representation sigma of a finite quotient. In particular sigma has
no invariant vector. For d>k use the exact representations

    U(s)=I_d,
    Theta(s)=I_(d-k) direct_sum sigma(s),
    A_0=I_d:C^d->C^d.

The initial operator contraction has normalized mass N0=1 and energy

    E0=sum_s ||Theta(s)A_0-A_0 U(s)||_(2,d)^2
       <=4h k/d.

Thus its energy can be arbitrarily small relative to its mass. However,
every exact intertwiner A from U to Theta has image in Theta^G, whose
dimension is d-k. If ||A||op<=1, then

    ||A||_(2,d)^2<=1-k/d.                             (HB1)

This holds for every replacement contraction, not merely the output
of heat flow. The defining defect is zero, so an O(delta^2) upper
bound for the necessary mass loss is impossible.

There is also an explicit energy version. Decompose A into its target
invariant and sigma rows. The Kazhdan bound, applied to the columns of
the sigma rows, gives

    E(A)>=kappa^2 ||A_sigma||_(2,d)^2,
    ||A||_(2,d)^2<=1-k/d+E(A)/kappa^2.                 (HB2)

For a positive-defect version replace the trivial input by scalar
phases U_t(s)=exp(i t c_s)I_d, choosing c_(s^-1)=-c_s. Choose the
coefficient of one elementary generator, for example x_13, nonzero,
and the others zero. A root relator with an x_13 term then has phase
exp(plus-or-minus i t), so delta_t is positive and comparable to |t|
for small nonzero t. On the sigma rows, the cochain operator changes
in norm by at most sqrt(h)max_s|exp(i t c_s)-1|. For sufficiently small
t its lower singular bound remains at least kappa/2. Therefore

    ||A||_(2,d)^2<=1-k/d+4E_t(A)/kappa^2.              (HB3)

Any contraction whose energy is O(delta_t^2) still loses at least
k/d-O(delta_t^2) of the original mass. The initial energy remains
small when k/d and t are small.

The same example obstructs a two-sided coefficient argument that
would force a full near-identity intertwiner between two close
approximate tuples: both tuples here are already exact at t=0, yet
their unmatched summands cannot intertwine. It does not obstruct
correcting the input by an independently chosen exact representation;
the input at t=0 is already exact.

## 2. Full correction on a fixed coarse HS basin is already global

Let G be a finitely presented Kazhdan group. Suppose there is eta0>0
such that every asymptotic tuple sequence within eta0 in normalized
generator HS distance of an exact same-dimensional representation
admits full flexible corrections. Then G is flexibly HS-stable for
arbitrary asymptotic sequences. It is enough to assume this basin
property around the trivial representation.

Choose a fixed integer m with 2/sqrt(m)<eta0. For an arbitrary tuple
U on C^d, form the tuple W on C^(md) given by

    W_s=U_s direct_sum I_((m-1)d).

Then

    max_s||W_s-I_(md)||_(2,md)<=2/sqrt(m)<eta0,
    delta(W)=delta(U)/sqrt(m).                        (HB4)

Apply the basin hypothesis to W_j. Write alpha_j for its exact
correction on C^(D_j), where D_j/(m d_j)->1, and let e_j->0 be its
normalized generator error relative to W_j direct_sum I_(D_j-md_j).
For the inclusion J_j of the original d_j coordinates,

    max_s||alpha_j(s)J_j-J_j U_(j,s)||_HS/sqrt(d_j)
      <=sqrt(D_j/d_j)e_j=:beta_j->0.                 (HB5)

The fixed amplification factor m is harmless. Rounding the original
d_j-dimensional almost invariant corner inside the genuine alpha_j
gives a full flexible correction of U_j, with generator error O(beta_j)
and relative padding O(beta_j^2). The required rounding calculation is
recalled below. Conversely global flexible stability plainly implies
the basin property, so the qualitative properties are equivalent.

If the proposed basin theorem has the stronger bounds

    e_j<=C delta(W_j),
    (D_j-md_j)/(md_j)<=C delta(W_j)^2,

then (HB4)--(HB5) give

    beta_j<=C delta(U_j) sqrt(D_j/(md_j))=O(delta(U_j)).

Consequently this basin theorem would imply global linear generator
error O(delta(U)) and quadratic relative padding O(delta(U)^2).
It is substantially stronger than the proved local first-vector
estimate, whose recovered vectors can lie in the added exact block.

### Original-rank rounding used in the transfer

For completeness, let alpha be any genuine finite-dimensional
representation, let J:C^d->H be an isometry, and assume the retained
column bound in (HB5) with beta. Put P=JJ*. Unitarity gives

    max_s||[alpha(s),P]||_HS^2<=2beta^2 d.

Project P onto the invariant space for genuine conjugation, obtaining
a positive contraction Z. The Kazhdan bound gives
||P-Z||_HS^2<=2beta^2d/kappa^2. For Q=1_[1/2,1](Z), invariance and
trace orthogonality give

    ||P-Q||_HS^2
      =Tr Z+Tr Q-2Tr(ZQ)
      <=2Tr(Z-Z^2)=2||P-Z||_HS^2
      <=4beta^2d/kappa^2.                            (HB6)

In particular |rank Q-d|<=4beta^2d/kappa^2. If rank Q<d, add a
trivial ambient representation and include that sector in the target
projection. If rank Q>d, put q=rank Q-d and extend J by q orthonormal
columns inside its original ambient space; compare these new input
columns with the trivial representation. Such columns exist because
the ambient dimension is at least rank Q. In either case the resulting
equal-rank projections differ in squared HS norm by at most twice
(HB6). Matching their principal vectors gives an isometry W with

    ||W-J_extended||_HS<=2sqrt(2)beta sqrt(d)/kappa.

In the rank Q>d case the newly added input columns need not intertwine
the original exact representation with the identity. Their generator
residual is at most 2sqrt(q)<=4beta sqrt(d)/kappa. Including this term,
the conjugated target's error before normalization is at most

    beta sqrt(d)+4beta sqrt(d)/kappa+2||W-J_extended||_HS.

The rank Q<=d case needs no added-input-column term. Thus the corrected
dimension D' and normalized error satisfy in both cases

    0<=(D'-d)/d<=4beta^2/kappa^2,
    error<=(1+(4+4sqrt(2))/kappa)beta
          <=(1+10/kappa)beta.                        (HB7)

This is the finite-dimensional retained-column form of the same
Kazhdan corner argument used in MSC. It introduces no dependence on
the original ambient dimension D_j or the dilution factor m.

## 3. The added exact mass is visible in the count exactly

For SL_5(Z), let N_(U,Q)(epsilon) denote regular-host spectral count,
and use the universal quotients from MSC16. For any U on C^d and m>=0,
if 2h epsilon^2/kappa^2<=1/2, then

    N_(U direct_sum I_m,Q_(2(d+m)))(epsilon)
      =N_(U,Q_(2d))(epsilon)+m.                       (HB8)

The rectangular coefficient space splits orthogonally by the two
source blocks. On the U block, MSC16 universality identifies the count
in the larger host with the count in Q_(2d); the former quotient
refines the latter. On the trivial block the coefficient action is
genuine regular translation with multiplicity m. Its invariant space
has dimension m, and its noninvariant spectrum is at least kappa^2/h,
strictly above the stated cutoff. This proves (HB8).

Thus dilution can supply a large coarse spectral count without
supplying any low-energy type for the original tuple. Neither this
identity nor the mass-loss example proves instability. They explain
why full correction, or almost complete mass recovery, cannot simply
be substituted for the actual conclusions of the curved Hodge theorem.
