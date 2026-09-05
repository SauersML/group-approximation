# Curved Hodge control transfers fixed-cutoff Schreier mass

Date: 2026-09-05. Analytic proof; no computation or builds.

For a finitely presented Kazhdan group, an approximate coefficient action
satisfies a degree-one Hodge inequality with an error controlled by its
normalized HS curvature and the operator norm of the cochain. A contractive
heat flow converts this into a linear first-vector estimate throughout a
uniform HS neighborhood of an exact representation. More significantly for
SL5, it transfers positive normalized spectral count at one fixed small
cutoff to positive count at cutoffs tending to zero. It does not create a
first vector when that fixed-cutoff count is absent.

## 1. Presentation conventions and the exact Hodge gap

Fix a finite presentation G=<S|R>, and put h=|S| and M=|R|. To agree with
MSC's symmetric connection convention, S may include both generator labels
and their formal inverse labels, but then R explicitly includes their
inverse-consistency relators. The tuples below evaluate those labels as
adjoints, so the added relator defects are zero. Without these rows,
independent cochains on both labels could have spurious first cohomology.

For unitary operators T_s on a Hilbert space, write

    (d0 v)_s = (T_s-I)v.

Let d1 be the finite Fox/word differential from S-cochains to R-cochains:
extend a cochain to the free group by f(ab)=f(a)+T(a)f(b) and
f(s^{-1})=-T_s^{-1}f(s), then take its values at the defining relators.
This is defined even when T does not factor through G, and telescoping gives

    (d1 d0 v)_r = (T(r)-I)v.                                  (CH1)

If T is genuine, ker d1 is the space of group cocycles and im d0 its
coboundaries. Property (T) gives H^1(G,pi)=0 for every unitary pi, by the
Delorme--Guichardet theorem; see
[Bekka--de la Harpe--Valette, Theorem 2.12.4](https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf).
Only full H^1 vanishing is used here, not H^2 or reduced cohomology.

There is a constant g>0, depending only on this presentation, such that
for every genuine unitary coefficient representation and every S-cochain f,

    ||d0* f||^2 + ||d1 f||^2 >= g ||f||^2.                     (CH2)

Proof: otherwise take genuine representations and unit cochains whose
left side tends to zero. Their Hilbert ultraproduct is a genuine G
representation, and the limiting unit cochain is a cocycle orthogonal
to every coboundary. Full H^1 vanishing makes it a coboundary, a
contradiction. All maps pass to the ultraproduct because their finite-word
coefficients have uniform bounds. Fix mu=g/2 from now on.

## 2. A uniform curved Hodge inequality

Let U_s act on C^d, let rho:G->U(D) be any genuine representation, and put

    delta = max_(r in R) ||U(r)-I||_(2,d),
    T_s(A) = rho(s) A U_s*,        A:C^d->C^D.

All rectangular HS norms in this section are divided by sqrt(d), the source
dimension normalization. Operator norms retain their usual normalization.
The maps T_s are Hilbert-unitary and preserve the rectangular operator norm.

There exist C<infinity and delta_*>0, independent of d,D,rho,U, such that
for delta<delta_* and every rectangular S-cochain f,

    mu ||f||_2^2 <= ||d0* f||_2^2 + ||d1 f||_2^2
                    + C delta^2 max_s ||f_s||op^2.            (CH3)

Here ||f||_2^2 is the sum over S, and the relation-cochain norm is the sum
over R. At delta=0 this follows immediately from (CH2).

Suppose the claimed uniform constants do not exist. Choose positive
delta_j<1/j and counterexamples to (CH3) with C=j, then normalize
||f_j||_2=1. Since all terms on its right are nonnegative,

    delta_j max_s ||f_(j,s)||op < sqrt(mu/j) -> 0.              (CH4)

In the normalized rectangular HS ultraproduct, let H_small be the closure
of classes with bounded HS representatives A_j satisfying
delta_j||A_j||op->0. Each T_s and its inverse preserves this subspace.
For a defining relator r,

    ||(T(r)-I)A_j||_2
       = ||A_j(U_j(r)*-I)||_2
       <= ||A_j||op delta_j -> 0.

Thus the restrictions define a genuine G action on H_small. The components
of f belong to H_small by (CH4). Passing the violated inequality to the
ultraproduct gives Hodge energy at most mu for its unit cochain. This
contradicts (CH2), whose lower bound is g=2mu. This proves (CH3).

The closure is important: H_small is a Hilbert coefficient space, even
though a fixed bound on representative operator norms is not imposed.
No action on the entire HS ultraproduct is claimed.

## 3. Contractive heat flow and quantitative mass retention

Let A_0:C^d->C^D be any operator contraction and set

    L0=d0* d0=sum_s(2I-T_s-T_s*),
    A_t=exp(-t L0) A_0,
    E(t)=||d0 A_t||_2^2,        N(t)=||A_t||_2^2.

The heat semigroup preserves the operator unit ball. Indeed

    exp(-t L0)
       = exp(-2ht) sum_(k>=0) (2ht)^k/k! K^k,
    K=(1/(2h))sum_s(T_s+T_s*),

and K is an operator-norm contraction. This remains true even though
the coefficient action is approximate.

Consequently max_s||(d0 A_t)_s||op<=2. Equation (CH1) and rho(r)=I give

    ||d1 d0 A_t||_2^2
       = sum_r ||A_t(U(r)*-I)||_2^2 <= M delta^2.

Apply (CH3) to f=d0 A_t and put K0=M+4C. Since the heat generator is
Hilbert self-adjoint and positive,

    E'(t)=-2||L0 A_t||_2^2 <= -2mu E(t)+2K0 delta^2,
    N'(t)=-2E(t).

Writing E0=E(0) and N0=N(0), integration yields

    E(t) <= E0 exp(-2mu t) + (K0/mu)delta^2,
    N(t) >= N0-E0/mu-(2K0/mu)delta^2 t.                        (CH5)

In particular t=log(1/delta)/mu gives energy O(delta^2) while the
additional curvature-dependent mass loss tends to zero. This is a
uniform finite-dimensional inequality; no time/dimension interchange
is implicit.

## 4. A uniform HS basin for the linear first-vector estimate

Suppose D=d, A_0=I_d, and

    max_s ||rho(s)-U_s||_(2,d) <= eta0,
    h eta0^2 <= mu/4.                                        (CH6)

Then N0=1 and E0<=h eta0^2. For all sufficiently small positive delta,
at the logarithmic time above (CH5) gives N(t)>=1/2 and

    E(t) <= (h eta0^2+K0/mu)delta^2.

For the connection Laplacian Delta=L0/h, its minimum Rayleigh quotient is
therefore at most

    [2 eta0^2+2K0/(h mu)]delta^2.                             (CH7)

For SL5, rho factors through Q_(2d). Decomposing rho into irreducibles,
at least one nonzero component of A_t has Rayleigh quotient no greater
than that of A_t. The regular Q_(2d) representation contains this type,
so (CH7) is the literal universal-host estimate required by MSC19.
Extra copies of rho's irreducible constituents are unnecessary for
this one-vector conclusion.

The radius eta0 is independent of dimension and is measured in normalized
HS norm, not operator norm. No estimate tying the distance to rho to delta
is assumed. However, existence of this coarse comparison rho is an input;
the theorem does not put arbitrary approximate tuples into this basin.
Diluting a tuple by an added exact block cannot remove that requirement
on the original tuple, since the recovered vectors may lie entirely in
the added block.

## 5. Fixed-cutoff count transfers to vanishing cutoffs in SL5

Use the universal regular host Q_(2d) and write

    N_U(epsilon)=rank 1_[0,epsilon^2](Delta_(Q_(2d),U)),
    a(epsilon)=2h epsilon^2/kappa^2,
    xi(epsilon)=sqrt(h)epsilon+2sqrt(a(epsilon)/(1-a(epsilon))).

Choose one fixed epsilon_*>0, depending only on presentation constants,
so a_*=a(epsilon_*)<=1/2 and

    gamma=h xi(epsilon_*)^2/[mu(1-a_*)] <= 1/4.                (CH8)

Let r=N_U(epsilon_*). When r=0 the conclusions below are vacuous. MSC14
gives an exact target Theta of dimension r and a contraction
A_0:C^d->C^r with

    N0=min(r,d)/d,       E0<=h xi(epsilon_*)^2 r/d,
    r/d<=1/(1-a_*).

For r<=d this is its polar coisometry. For r>d take the first d columns
of its polar-completed unitary; restricting the padded-input edge error
gives the displayed bound. In both cases E0/mu<=gamma N0. Since r<=2d,
Theta factors through Q_(2d).

Apply (CH5) with t=log(1/delta)/mu. To convert retained mass to count,
choose an HS-orthonormal basis T_a of exact intertwiners from Theta to
the regular Q_(2d) representation. The regular multiplicity identity is
sum_a T_a* T_a=I_r. As in MSC15 and MSC18,

    F_t=sum_a |T_a A_t><T_a A_t| <= I,
    Tr F_t=d N(t),           Tr(Delta F_t)=d E(t)/h.

The first inequality follows because right multiplication by the
operator contraction A_t takes an orthonormal family to a Bessel family.
Spectral truncation thus yields, for every eta>0,

    N_U(eta)/d >= N(t)-E(t)/(h eta^2).

Combining the estimates gives a constant C1 such that all sufficiently
small-defect tuples satisfy

    N_U(eta)/d >= (1-gamma)min(N_U(epsilon_*)/d,1)
                 -C1 delta^2 log(1/delta)-C1 delta^2/eta^2.    (CH9)

All constants and the small-defect threshold are uniform in d and U.
In particular, after increasing C1,

    N_U(sqrt(delta))/d
       >= (3/4)min(N_U(epsilon_*)/d,1)-C1 delta.                (CH10)

If N_U(epsilon_*)/d>=b>0 along a sequence, this produces positive
normalized count at a vanishing cutoff. For a fixed b it also produces
positive count at cutoff L_b delta by choosing L_b sufficiently large
in (CH9). The factor L_b may depend on b. No uniform microscopic
one-vector estimate is inferred when b tends to zero.

## 6. Consequence for the maximal residual, and the remaining gap

The earlier maximal-correctable-mass argument provides a hypothetical
unstable canonical residual W_j with

    lim_(eta down to 0) limsup_j N_(W_j)(eta)/d_j=0.

Equation (CH10) strengthens this to

    N_(W_j)(epsilon_*)/d_j -> 0                               (CH11)

at the one fixed positive cutoff from (CH8). Indeed, a subsequence
with fixed-cutoff count bounded below would give positive count at
cutoff sqrt(delta_j)->0, contradicting the preceding iterated limit.
This is a fixed gap in normalized spectral density. It is not a
positive lower bound for the smallest eigenvalue: a vanishing-density
family of very small eigenvalues is still allowed.

For the original existence route, it would now suffice to prove that
every canonical approximate SL5 sequence has positive normalized count
at this fixed cutoff on some subsequence. No such lower count theorem
is established here. The heat flow improves a supplied coarse mass;
it does not manufacture that mass from the defining relations alone.

The independent audit confirmed the curved ultraproduct estimate, the
heat constants, and the generator/inverse consistency convention. The
operator-neighborhood argument originally motivating the proof is
subsumed by the stronger HS basin in Section 4.
