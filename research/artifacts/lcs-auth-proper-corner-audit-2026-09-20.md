# Proper controlled-Pauli corners: a surviving local corner and a factorial obstruction

Date: 2026-09-20. Follow-up to `lcs-auth-controlled-form-audit-2026-09-20.md`.
No computation or build was run. This note does not construct a HALT-hard
source and does not refute the perfect-completeness LCS target.

## 1. The previous tensor model retains a substantial one-atom corner

Start with the honest controlled-Pauli model on `C^2 tensor K`, with
projection p of normalized trace t:

    U=(1-p)+Xp,   V=(1-p)+Zp,   s=1-2p,   [X,Z]=-I.

Take an odd number n of tensor factors, some possibly complex-conjugated.
In the latter case conjugate the source control too. The Pauli matrices
X and Z are real, and all controls still have trace t. Let

    X_* = product_i X_i,    Z_* = product_i Z_i.

The joint control branches are a in `{0,1}^n`, of weight
`t^|a| (1-t)^(n-|a|)`. On branch a, put S={i:a_i=1}; then

    U_* = product_(i in S) X_i,
    V_* = product_(i in S) Z_i,
    s_* = (-1)^|S| I.

We seek a corner with the parity readout `q=(1-s_*)/2` and literal
controlled U_*,V_* relative to X_*,Z_*.

If |S| is even, use T=S; if |S| is odd, use its complement T. In both
cases |T| is even. Define

    G_X = product_(i in T) X_i,
    G_Z = product_(i in T) Z_i,
    E_a = (1+G_X)(1+G_Z)/4.                           (1)

The two G operators commute. They also commute with X_*,Z_*,U_*,V_*.
For example their commutator signs against the opposite-type anchor are
`(-1)^|T|=1`; against the port the relevant intersection has even size.
Thus E_a is a reducing projection for these four ports.

On E_a the two gauge operators are identity. For even |S| this makes
U_*=V_*=I, and for odd |S| it makes U_*=X_*, V_*=Z_*. These are exactly
the intended controlled forms for the parity readout.

When T is nonempty, G_X,G_Z and G_X G_Z are nonidentity Pauli words,
so E_a has normalized trace 1/4. When T is empty, E_a=I. The latter
case occurs precisely on the all-zero and all-one branches. Summing
the branch projections times E_a gives a projection E with

    tr(E) = 1/4 + (3/4)[(1-t)^n+t^n] >= 1/4.          (2)

It commutes with X_*,Z_*,U_*,V_*,s_*. The compressed parity projection
`q_E=E(1-s_*)/2` gives the exact controlled forms on E.

For this fixed parity readout E is the maximal simultaneous good corner:
the desired identities require both G operators to be +1 on every
branch, so their simultaneous kernel projection is exactly (1). This
argument does not require an arbitrary competing corner to preserve
the individual control branches; the equations' common kernel itself
is block diagonal in them.

Consequently, iterating the odd-tensor countermodel alone does NOT make
the one-atom usable corner vanish. Its weight tends to 1/4 for 0<t<1.
The same lower bound holds in direct sums of these odd tensor models.
The projection E need not commute with other atoms, context gates, or
auxiliary generators. A common corner for an entire source is a separate
problem, not solved by (2).

## 2. An explicit scalar-preserving amplification

Let H be a countable subgroup of U(d), with its faithful inclusion rho.
It may be the image of a larger presented group in one honest model.
Set

    Z_sc = H intersect {lambda I_d: |lambda|=1},
    Q = H/Z_sc,
    chi(h) = tr_d(rho(h)).

Assume Q is ICC: every nonidentity element has an infinite conjugacy
class. This is an additional group-image hypothesis, not an automatic
consequence of having an honest controlled model.

Define finite-dimensional representations of H by

    R_m = rho tensor [1 direct-sum (rho tensor conjugate(rho))]^(tensor m).
                                                               (3)

Their dimensions are `d(1+d^2)^m`. Every ordinary group relation is
preserved exactly. Every scalar central value of rho is preserved too:
both summands inside brackets send a scalar lambda I to identity.
In particular an initial mark J=-I remains -I.

The normalized characters are

    tau_m(h) = chi(h) [(1+d^2 |chi(h)|^2)/(1+d^2)]^m.   (4)

A unitary has normalized trace of modulus one exactly when it is scalar.
Thus (4) converges pointwise to

    tau_sc(h) = lambda,  if rho(h)=lambda I_d;
                0,      otherwise.                  (5)

Choose a section of H->Q. Its multiplication defects are scalar elements
of Z_sc; applying their scalar character gives a circle-valued two-cocycle
sigma on Q. The GNS algebra of (5) is the twisted group von Neumann
algebra `L_sigma(Q)` with its canonical trace. This identification follows
directly from the orthonormal coset basis and twisted left multiplication.

It is a factor under the ICC hypothesis. For a central element its Fourier
coefficient magnitudes are constant on each conjugacy class of Q, since
twisted conjugation changes only phases. Square summability forces every
coefficient on a nonidentity, infinite conjugacy class to vanish. The
center therefore consists of scalars.

The scalar subgroup Z_sc may be infinite. What is fixed is its actual
scalar character in rho. It is not legitimate to replace this condition
by an unverified assertion that the original presentation modulo J is ICC.

## 3. Positive-weight globally reducing good corners disappear

Fix a finite group-algebra polynomial `a in C[H]` such that

    tau_sc(a^*a)>0.                                    (6)

Let P_m be projections in the matrix spaces of (3). Suppose

    ||[P_m,R_m(h)]||_2 -> 0   for every h in H,
    ||R_m(a) P_m||_2 -> 0.                             (7)

Then

    tr(P_m) -> 0.                                      (8)

Exact globally reducing corners annihilating a are a special case.
For a finitely generated H, checking the first condition on a generating
set suffices by the telescoping commutator identity for a fixed word.

Here is a proof including the positive-weight quantifier. Suppose some
subsequence has `tr(P_m)>=c>0`. On the full group C*-algebra define

    phi_m(x)=tr(P_m R_m(x)).

These are positive functionals with `0<=phi_m<=tau_m`, and their norms
are at most one. Since H is countable, take a weak-star convergent
subsequence. Its limit phi satisfies

    0<=phi<=tau_sc,    phi(1)>=c.

The first part of (7) makes phi tracial: cyclicity of the matrix trace
and Cauchy--Schwarz bound each traciality defect by the relevant
normalized-HS commutator defect. Domination by tau_sc makes phi a normal
functional on its GNS von Neumann algebra. Its density with respect to
tau_sc is a positive contraction; traciality makes that density central.
Because the algebra is a factor, `phi=c' tau_sc` for `c'>=c`.

But the second part of (7) gives

    phi(a^*a)=lim ||R_m(a)P_m||_2^2=0,

contradicting (6). This proves (8). This qualitative argument alone
supplies no explicit decay rate; Section 6 supplies a finite-test bound.

## 4. Application to the controlled-Pauli defect

Suppose the actual image H in Section 2 contains commuting involutions
X,U from an honest nontrivial controlled model. Set

    b=(1+X)(1-U)/4.                                    (9)

It is a projection in C[H]. Assume, explicitly, that X,U,XU are all
nonscalar in the actual image. Their scalar cosets are then distinct,
and (5) gives

    tau_sc(b^*b)=tau_sc(b)=1/4.                        (10)

For the honest model `U=(1-p)+Xp` on `C^2 tensor K`, with `0<tr(p)<1`,
these nonscalarity conditions hold: X is Pauli, U is a nontrivial
controlled reflection, and XU is the reflection controlled by 1-p.
Although b evaluates to zero in this honest matrix representation, it
is NOT zero in the canonical twisted group algebra, as (10) proves.
This distinction is essential to the argument.

Any exact corner reducing the group image and satisfying a literal
controlled-X identity for the compressed U,X has bP=0, irrespective
of which projection is used as its control. The reason is the same
identity `e_+(X)[(1-q)+Xq-I]=0` used in the previous audit.
Therefore, if this honest image also has ICC scalar quotient, (8)
precludes a uniform positive normalized-trace lower bound for such
globally reducing corners along (3). Conditions (7) also cover
asymptotically reducing, asymptotically annihilating corners.

The ICC condition can instead be imposed on a subgroup generated only
by the decoder's necessary ports, provided the corner asymptotically
commutes with ALL generators of that subgroup and the character limit
is restricted to it. It cannot be imposed on a larger auxiliary group
while allowing the corner to ignore those auxiliaries: then phi need
not be tracial on the factorial algebra used in the proof.

## 5. Three explicit controls supply the port-image hypothesis

The ICC hypothesis can be verified for an explicit four-dimensional
honest controlled model, without adding irrelevant auxiliary generators.
On the two-dimensional source space put

    p_0 = |v_0><v_0|,       v_0=(0,1),
    p_1 = |v_1><v_1|,       v_1=(-4,3)/5,
    p_2 = |v_2><v_2|,       v_2=(4i,3)/5.              (11)

Use the honest U_j,V_j for these three controls, and the common anchor
`X=X_Pauli tensor I_2`, `Z=Z_Pauli tensor I_2`. Let H be the actual
subgroup of U(4) generated by these eight matrices. All their entries
are in Q(i). Three independent binary PVM contexts admit this model;
no cross-context commutation is asserted.

Write source Pauli matrices as sigma_x,sigma_y,sigma_z. Let theta be
the angle with cos(theta)=3/5 and sin(theta)=4/5. It is an irrational
multiple of pi: otherwise exp(i theta) would be a root of unity, making
its sum with its inverse, 6/5, a rational algebraic integer, impossible.
The source reflections h_j=I-2p_j obey

    h_0 = sigma_z,
    h_1 = cos(2theta) sigma_z + sin(2theta) sigma_x,
    h_2 = cos(2theta) sigma_z + sin(2theta) sigma_y,
    h_0 h_1 = exp(i 2theta sigma_y),
    h_0 h_2 = exp(-i 2theta sigma_x).                  (12)

On the ancilla X=-1 eigenspace, U_j acts as h_j, and on X=+1 it is
identity. Thus powers of U_0 U_1 and U_0 U_2 generate dense one-parameter
source rotations about two different axes, restricted to X=-1. The
closure contains SU(2) on that plane. Similarly the V products give
SU(2) on the ancilla Z=-1 plane.

Here is the full Lie-algebra calculation, so density is not inferred
merely from noncommutativity. Write

    P=(I-X_Pauli)/2,    Q=(I-Z_Pauli)/2.

The Lie algebra of the compact closure contains
`iP tensor sigma_j` and `iQ tensor sigma_j` for all three source Paulis.
Commutators with different source indices give
`i{P,Q} tensor sigma_j`, up to nonzero real constants. Since

    {P,Q}=P+Q-I/2,

their real linear span contains `iI tensor sigma_j`, and then
`iX_Pauli tensor sigma_j` and `iZ_Pauli tensor sigma_j`. Commuting
the latter two with the same source index also gives `iY_Pauli tensor I`.

Now V_0 is the usual two-qubit controlled-Z matrix. Conjugation by V_0
preserves the Lie algebra of the closure, and sends

    X_Pauli tensor sigma_x  to  Y_Pauli tensor sigma_y.

Bracketing with the already available source rotations gives
`iY_Pauli tensor sigma_j` for every j. Commuting these with the
X- and Z-type mixed terms of the same source index yields
`iZ_Pauli tensor I` and `iX_Pauli tensor I`. We therefore have all
15 traceless two-qubit Pauli directions: the Lie algebra contains su(4).
The compact closure contains SU(4), and its projective image is all PU(4).

This proves that H/Z_sc is ICC. If a nonidentity projective element had
a finite conjugacy class, its centralizer in H/Z_sc would have finite
index. The closure of that centralizer in PU(4) has finite index and
therefore is all PU(4), because PU(4) is connected. The element would
then be central in PU(4), whose center is trivial, a contradiction.

Apply (3) with d=4. The resulting exact representations have dimensions

    4 times 17^m.                                     (13)

Every one has the same marked Pauli sign. For the port U_0, take b from
(9); all three of X,U_0,XU_0 are nonscalar, so (10) holds. It follows
that every sequence of corners asymptotically reducing these eight
specified ports and asymptotically annihilating b has normalized trace
tending to zero. In particular this holds for exact common reducing
corners on which even U_0 has literal controlled-X form with an arbitrary
non-affine projection readout. Requiring all six ports to have their
honest controlled forms is stronger still.

There is no contradiction with (2). That one-atom corner generally fails
to reduce the other two atoms' ports.
Nor are all common good corners absent: choosing the trivial summand in
each bracket of (3) gives a copy of the original honest model, of relative
weight `17^(-m)` in (13). The theorem rules out a uniform positive weight,
not the existence of arbitrarily small exact good corners.

If an ordinary-group completion extends this honest port model after an
amplification by an identity multiplicity space, tensor its ENTIRE honest
representation as in (3). All extra relations remain exact. Restricting
the resulting characters to the port subgroup gives the same scalar limit
and the same vanishing-corner conclusion. In that case the dimension d
in (3)--(4) is the dimension of the full honest representation, not
necessarily four. The relevant projective port image remains unchanged.

## 6. A finite-test quantitative bound

The following quantitative refinement was supplied by the root lane and
checked independently against its constants. It uses finitely many
explicit conjugators, so it does not require estimating an infinite join
of supports.

Let `F={X,U,XU}` in the scalar quotient Q. Choose g_1,...,g_N in H
such that their conjugates of F in Q are pairwise disjoint. Put

    b_i=g_i b g_i^-1,
    A=(1/N) sum_i b_i,        D=A-1/4.

Twisted Fourier orthogonality and (9) give

    tau_sc(D^2)=3/(16N),
    ||D||_(coefficient l1)<=3/4,
    ||D^2||_(coefficient l1)<=9/16.                   (14)

For each nonscalar h in the finite support of D^2 put
`r_h=(1+d^2 |chi(h)|^2)/(1+d^2)`, and let beta be their maximum.
Then beta<1. If there is no nonscalar term the error term below is zero.
Scalar terms have exactly the same value under tau_m and tau_sc, and
(4) bounds every remaining character term by beta^m. Therefore

    ||R_m(D)||_2^2 <= 3/(16N)+(9/16) beta^m.           (15)

For any projection P define

    epsilon = ||R_m(b)P||_2
                + max_i ||[P,R_m(g_i)]||_2.

Conjugating b shows `||R_m(b_i)P||_2<=epsilon`, hence
`||R_m(A)P||_2<=epsilon`. Since `A=D+1/4`, the triangle inequality
and (15) yield

    sqrt(tr(P)) <= 4 epsilon + sqrt(3/N+9 beta^m).     (16)

For an exact globally reducing good corner this specializes to

    tr(P) <= 3/N+9 beta^m.                            (17)

ICC supplies the required finite conjugators for every N. A short proof
avoids importing a finite-coset covering theorem. The conjugation action
on `l2(Q minus {1})` has no invariant vectors, because all its orbits
are infinite. For a finite set F the closed convex hull of the orbit
of its indicator has unique minimum-norm vector; invariance and the
absence of invariant vectors make that vector zero. For any finite
already-used set E, a convex combination can therefore have inner
product less than one with its indicator. Each individual inner product
is the nonnegative integer `|gFg^-1 intersect E|`, so one conjugate has
intersection zero. Induction chooses the desired N disjoint conjugates.

For the explicit matrices (11), the conjugators can in principle be
found by enumerating words and checking projective equality of rational
complex matrices. Their existence ensures this finite search terminates
for each N. The resulting beta is also exactly computable from those
matrices. No conjugator search was run here, and no polynomial bound on
the search or on the resulting dimensions is claimed.

## 7. Exact scope for a HALT-positive source

A dimension-independent positive corner weight is useful because
renormalizing its trace magnifies a normalized-HS error by the reciprocal
square root of that weight. Section 1 shows such weight survives the
basic single-atom tensor attack. Section 3 gives a different obstruction
under stated factorial-image and reducing-corner hypotheses.

Section 5 supplies a fixed honest three-control port image satisfying
the additional hypothesis, and rules out a universal positive-weight
common reducing-corner authentication theorem for these literal ports.
It does NOT construct a HALT-positive source reduction. The three binary
PVMs are themselves a trivial satisfiable constraint system. They can be
adjoined as an independent satisfiable component without changing another
system's satisfiability, but a compiler need not authenticate unused ports.
No hardness conclusion is inferred from this padding observation.
Requiring a completion to preserve this particular honest matrix model
is stronger than merely requiring existence of some perfect model on
every YES instance. The latter, weaker completeness promise alone does
not place the countermodels constructed here in that completion.

ICC was proved by the displayed Lie-algebra argument, not inferred from
noncommuting measurements, a Pauli anchor, or a universal-gate label.
Nor is a model-dependent decoder assumed to compress every group generator:
the new obstruction expressly requires reduction of the stated port set.
Nonreducing compressions, replacement matrix-algebra operators, choosing
different anchors, or substantial loss remain outside the theorem.

Repository checks included the controlled-Pauli and CE-affine quotient
notes, `group-corner-decoders-split-into-coset-and-matrix-readouts`, and
`canonical-marked-corner-nonamenable-density-vanishes`. The last concerns
adjoint-space low-energy density from nonamenability; Section 3 instead
uses a factorial limiting trace and a fixed nonzero polynomial on ordinary
representation corners. All calculations here are symbolic. No literature
priority claim is made for the dominated-trace argument.

An external reconnaissance check on 2026-09-20 found the established
universal-gate literature, including the primary author abstract of
[Barenco et al., Elementary gates for quantum computation](https://arxiv.org/abs/quant-ph/9503016).
Controlled gates and universality are not claimed as new. Section 5 proves
its particular eight-generator density statement directly; it does not
import an unspecified universality theorem. The maintained new result is
the application of that explicit port image and scalar-preserving
amplification to uniform reducing-corner authentication. The primary
[Taller--Vidick v2 introduction](https://arxiv.org/html/2507.22444v2#S1)
was also rechecked this day for the surrounding perfect-completeness
boundary. No exhaustive literature-priority claim is made.

## 8. Independent review

On 2026-09-20 the hardness-audit sibling independently checked Sections
1--4, including maximality of the single-atom kernel corner without
branch-preserving assumptions, the dominated factorial-trace argument,
and the nonzero canonical polynomial. The review passed.

The root independently checked Sections 5--6, including all reflection
signs, all fifteen Lie-algebra directions, projective ICC, the variance
and coefficient-l1 constants, and the convex-hull displacement lemma.
The hardness-audit sibling then separately reviewed the same new sections
and passed them, also checking the effective rational-matrix word search
claim and the fixed-port scope. No computation or formal verification
is claimed by either review.
