# Stationary curvature and an operator-flat gradient basin

Date: 2026-09-05. Analytic result; no computation or builds.

For SL5, almost-stationarity of defining-relator energy forces the tuple
itself into the hard-angle curvature normal form, without first changing
its generators. In particular there is a dimension-independent
operator-relator neighborhood in which the energy gradient dominates
the square root of the energy. Nonexact critical points cannot occur
there. This does not make hard supports invariant or prove that a
gradient trajectory remains in that neighborhood.

## 1. Hypotheses, energy, and stationarity convention

Use the twenty distinct elementary generators x_ij of SL5 and a fixed
finite presentation on them, with inverse letters evaluated as adjoints.
More generally the proof applies to a finitely presented group with
ordinary H^2(G,H_pi)=0 for every unitary Hilbert representation and a
generating menu whose distinct nonidentity group elements can be assigned their
literal one-letter section words. The generator menu is fixed throughout.

For U in U(d)^S define

    E_r(U)=U(r)-I,
    delta(U)=max_r ||E_r(U)||_(2,d),
    F(U)=sum_r ||E_r(U)||_(2,d)^2.

All Hilbert norms and traces are normalized by d. On tangent vectors
X=(X_s), with X_s skew-Hermitian and U_s(t)=exp(t X_s)U_s, use the
real Hilbert metric sum_s Re tr_d(X_s*Y_s). Let grad F be the gradient
in these left logarithmic coordinates. Thus

    dF_U(X)=sum_s Re tr_d((grad F)_s* X_s).

Writing M=|R|, one has delta^2<=F<=M delta^2. This is ordinary
finite-dimensional smooth stationarity, not a weak notion defined only
against bounded-operator test matrices.

## 2. Almost-stationarity kills all low-angle curvature

Suppose delta_j=delta(U_j)>0 tends to zero and

    ||grad F(U_j)||_2/delta_j -> 0.                             (SG1)

Then, for the original tuples themselves,

    lim_(t down to 0) limsup_j max_r
      ||(E_r(U_j)/delta_j) 1_(|E_r(U_j)|<=t)||_2 = 0.          (SG2)

In particular, for every epsilon>0 there are projections P_j and a
finite C_epsilon, eventually satisfying

    tr_d(P_j)<=C_epsilon delta_j^2,
    max_r (||E_r(U_j)(I-P_j)||_2
           +||(I-P_j)E_r(U_j)||_2)<=epsilon delta_j.           (SG3)

No generator modification precedes these conclusions. The projections
are joins of spectral supports and are not asserted reducing.

### Proof of (SG2)

Fix an ultrafilter and the Hilbert ultraproduct of normalized matrix L2
spaces. Let K_delta be the closure of classes represented by L2-bounded
sequences A_j with delta_j||A_j||op->0 along the ultrafilter, and let P
be its orthogonal projection. Each fixed section defect D-I has HS
size O(delta_j), by a fixed van Kampen filling. Its multiplication
error on a core representative is at most O(delta_j||A_j||op),
which tends to zero. Thus adjoints of section words give a genuine
G action on K_delta. The subspace and its orthogonal complement
are invariant under these unitaries, so P commutes with them.

Choose word sections q_g with q_e empty and q_(x_ij)=x_ij. In particular
the section values on this generator menu are exactly the input
unitaries, so there is no additional hard section-replacement error.
Project the normalized pair curvature onto K_delta. The exact
associativity identity and the quadratic-product orthogonality estimate
make that projection a skew-Hermitian 2-cocycle. Ordinary H^2 vanishing
provides a skew cochain b whose coboundary is this projected curvature.
Choose generator representatives b_(j,s) with

    ||b_(j,s)||_2=O(1),       delta_j||b_(j,s)||op->0.

The inverse-letter variations are the actual adjoints of the generator
variations; they are not additional independent choices.

For a fixed defining word r, let L_(j,r)(b_j) denote its left logarithmic
derivative: a signed finite sum of conjugates of the b_(j,s) by prefix
words. Put c_r=[E_r(U_j)/delta_j]. Finite-word expansion of the same
cohomological correction used in QRC gives

    [L_(j,r)(b_j)]=P c_r.                                    (SG4)

Indeed the corrected word with generators exp(-delta_j b_(j,s))U_(j,s)
has normalized error c_r-[L_(j,r)(b_j)] in K_delta^perp, while the
derivative class belongs to K_delta. The expansion remainder is o(1)
in normalized L2: delta_j||b_(j,s)||op->0 controls the exponential
Taylor terms and their products with old fixed-word defects.

Consider the genuine differentiable curve

    U_(j,s)(t)=exp(-t delta_j b_(j,s))U_(j,s).

Its initial tangent has Hilbert norm O(delta_j), so (SG1) implies

    F'(U_j(t))|_(t=0)/delta_j^2 -> 0.                         (SG5)

On the other hand, the exact derivative of the relator matrix at zero is
-delta_j L_(j,r)(b_j) U_j(r). Its normalized limit after division by
delta_j equals -P c_r: the difference from -L_(j,r)(b_j) has L2 norm
at most a fixed multiple of delta_j max_s||b_(j,s)||op, which tends
to zero. Thus direct differentiation of the squared norm gives

    lim F'(U_j(t))|_(t=0)/delta_j^2
       = -2 sum_r Re <c_r,P c_r>
       = -2 sum_r ||P c_r||_2^2.                             (SG6)

Equations (SG5)--(SG6) force every P c_r to vanish. The spectral-angle
characterization of K_delta orthogonality now gives (SG2): a low-angle
piece retaining positive mass at cutoffs t_j->0 would itself be a
nonzero K_delta test vector pairing positively with c_r. The argument
applies after any subsequence and ultrafilter, hence gives the displayed
ordinary limsup, not only a selected subsequence assertion.

For (SG3), choose a fixed t small enough in (SG2) and join the
projections 1_(|E_r(U_j)|>t). Their trace is at most M delta_j^2/t^2.
The errors are normal, so the complementary left and right norms are
both controlled by the corresponding low-angle truncations.

## 3. A uniform gradient-dominance neighborhood

There exist t0,c0>0, depending only on the fixed presentation and group,
such that every dimension and every tuple satisfying

    max_r||U(r)-I||op < t0

obey

    ||grad F(U)||_2 >= c0 delta(U)
                    >= (c0/sqrt(M))sqrt(F(U)).                (SG7)

Proof: otherwise take positive-defect counterexamples with operator
relator defect less than 1/j and gradient norm less than delta_j/j.
Then delta_j->0 and (SG1) holds. For any fixed positive t, eventually
every defining error lies entirely below t. Consequently the maximum
low-angle norm in (SG2) equals 1, contradicting that conclusion.
The zero-defect case of (SG7) is automatic.

In particular, any critical tuple in this operator-relator neighborhood
is exact. This rules out a sequence of nonexact stationary tuples whose
largest actual relator angle tends to zero. It does not rule out critical
tuples with hard curvature on very small subspaces.

## 4. Gradient flow, first exit, and a hybrid exact-correction radius

Set c_PL=c0/sqrt(M). Along negative gradient flow that remains in the
open neighborhood from Section 3,

    dF/dt=-||grad F||_2^2 <= -c_PL^2 F.

Before the first exit time, the total normalized-HS Riemannian length is
bounded by

    integral ||grad F||_2 dt
       <= (2/c_PL)sqrt(F(U_0)).                              (SG8)

To see this, use dF/dt=-||grad F||^2 and
||grad F||>=c_PL sqrt(F), then integrate from the final energy up to
the initial energy. The product unitary group is compact, so the smooth
flow exists globally in each fixed dimension.

If it never exits the neighborhood, exponential energy decay and finite
length give an exact limiting tuple at HS distance O(delta(U_0)). If
it exits, a defining relator reaches operator distance t0 from identity,
possibly on only a very small subspace, while the total HS motion is
still O(delta(U_0)). The HS length estimate does not prevent this exit:
it gives no dimension-independent control of operator norm.

There is nevertheless a useful estimate on the time and energy of an
exit. Write alpha(t)=max_r||U_t(r)-I||op. Let n_s be the total number
of occurrences of generator s or its inverse in the fixed relator list,
and ell the longest relator length. The left-coordinate gradient of
`2-2 Re tr U(r)` is a sum of conjugates of twice the skew part of U(r),
with one summand for each occurrence. Hence

    ||(grad F)_s||op <= 2 n_s alpha(t).

Along the negative gradient flow, fixed-word differentiation therefore
gives the upper Dini-derivative bound

    D^+ alpha(t) <= C_R alpha(t),
    C_R=2ell max_s n_s,
    alpha(t)<=alpha(0) exp(C_R t).                            (SG9)

These bounds use the normalized trace metric: its gradient contains no
extra dimension factor. Take the presentation to have a nonempty relator
list, so C_R>0. If 0<alpha_0=alpha(0)<t0 and tau is its first exit,

    tau >= C_R^{-1} log(t0/alpha_0),
    F(U_tau) <= F(U_0)(alpha_0/t0)^theta,
    theta=c_PL^2/C_R >0.                                    (SG10)

At an exit, one relator has operator error t0 and thus normalized squared
HS error at least t0^2/d. Consequently the strict hybrid condition

    d F(U_0)(alpha_0/t0)^theta < t0^2                         (SG11)

precludes exit. Under (SG11), negative gradient flow converges to an
exact representation in the original dimension, with generator HS
distance bounded by (SG8). No additional projection surgery is needed.
For example, since F(U_0)<=M alpha_0^2, the explicit sufficient
dimension-dependent basin

    M d alpha_0^(2+theta) < t0^(2+theta),   alpha_0<t0          (SG12)

implies this same-dimensional correction. The constants are uniform in
d but may be nonconstructive. The alpha_0=0 case is already exact.

Thus (SG7) is a real descent estimate but not a stability theorem. It
does not establish that all low-defect local minima arise by compressing
exact irreducibles, does not turn spectral supports into invariant
subspaces, and does not supply a finite-dimensional spectral seed for
an arbitrary canonical residual. Its concrete implication for that
search is that any stationary obstruction must already carry hard-angle
curvature; uniformly operator-small stationary obstructions are excluded.
