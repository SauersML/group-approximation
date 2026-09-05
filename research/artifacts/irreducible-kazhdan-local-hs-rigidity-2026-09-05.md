# Irreducible Kazhdan representations have a uniform HS rigidity basin

Let G=<S|R> be a fixed finitely presented Kazhdan group. There are
eta0,L>0, depending only on the presentation and Kazhdan data, such
that the following holds in every dimension d. If rho:G->U(d) is
irreducible and an inverse-compatible tuple U satisfies

    max_s||U_s-rho(s)||_(2,d)<=eta0,
    delta=max_(r in R)||U(r)-I||_(2,d),

then some unitary V in U(d) satisfies

    max_s||U_s-V* rho(s)V||_(2,d)<=L delta.             (IR1)

The correction has the original dimension and belongs to the unitary
conjugacy class of the supplied rho. No H2 vanishing or finite-image
assumption is needed. The radius eta0 is in normalized HS norm, not
operator norm. No claim that V is O(delta)-close to the identity is
made or needed.

## 1. Heat retains a nonzero contraction at linear defect energy

Use the presentation and inverse-consistency conventions of
`kazhdan-approximate-coefficients-have-curved-hodge-control`. Let
h=|S|, M=|R|, and let mu,C_H,delta_H be its uniform constants. Put

    K0=M+4C_H,
    eta0=min(1/4,sqrt(mu/(4h))),
    B=h eta0^2+K0/mu.

On M_d use T_s(A)=rho(s)A U_s*, d0_s=T_s-I, and
L0=d0*d0. Starting with A_0=I_d, let A_t=exp(-tL0)I_d. With
all HS quantities normalized by d, write

    E(t)=sum_s||rho(s)A_t-A_t U_s||_2^2,
    N(t)=||A_t||_2^2.

The initial energy is at most h eta0^2 and initial mass is one.
The curved Hodge heat theorem gives ||A_t||op<=1 and

    E(t)<=h eta0^2 exp(-2mu t)+(K0/mu)delta^2,
    N(t)>=1-h eta0^2/mu-(2K0/mu)delta^2 t.             (IR2)

Choose delta_1 in (0,min(delta_H,e^(-1))) so small that

    (2K0/mu^2)delta^2 log(1/delta)<=1/4
                       for 0<delta<delta_1.

At t=log(1/delta)/mu, put A=A_t. Then

    ||A||op<=1,       c:=||A||_2^2>=1/2,
    sum_s||rho(s)A-AU_s||_2^2<=B delta^2.              (IR3)

All thresholds and constants are independent of d and rho.

## 2. Irreducibility makes the retained Gram almost scalar

Put Q=AA*. Since both rho(s)A and AU_s are contractions, expanding
their two products gives

    ||rho(s)Qrho(s)*-Q||_2
       <=2||rho(s)A-AU_s||_2.

The invariant matrices for genuine conjugation by rho are scalar,
by irreducibility. Their orthogonal projection sends Q to
tr_d(Q)I=cI. The Kazhdan bound therefore gives

    ||Q-cI||_2<=2sqrt(B)delta/kappa.                  (IR4)

Normalize T=A/sqrt(c). By c>=1/2,

    ||TT*-I||_2<=4sqrt(B)delta/kappa.

Complete the polar factor of the square matrix T to a unitary V.
In a singular-value decomposition, for every singular value s>=0,
|s-1|<=|s^2-1|. Thus even if T is singular,

    ||T-V||_2<=||TT*-I||_2<=4sqrt(B)delta/kappa.        (IR5)

There is no missing-rank or padding term: T is square and its two
null spaces have the same dimension. Using (IR3) and (IR5),

    ||rho(s)V-VU_s||_2
      <=||rho(s)T-TU_s||_2+2||T-V||_2
      <=sqrt(B)(sqrt(2)+8/kappa)delta.                (IR6)

Conjugating by V proves (IR1) at small positive defect with
L_small=sqrt(B)(sqrt(2)+8/kappa).

## 3. Zero defect and the full basin statement

If delta=0, the coefficient action is genuine. The finite-dimensional
heat flow converges to the projection A_infinity of I onto ker L0.
Equation (IR2) gives ||A_infinity||_2^2>=3/4, so it is a nonzero
exact intertwiner from U to rho. Schur's lemma makes
A_infinity A_infinity*=cI with c>0. Since the source and target both
have dimension d, A_infinity/sqrt(c) is unitary and conjugates rho
exactly to U. This proves (IR1) with zero right side.

For delta>=delta_1, choose V=I. The original basin assumption gives
error at most eta0<=(eta0/delta_1)delta. Hence (IR1) holds throughout
the stated basin with

    L=max(L_small,eta0/delta_1).

The small-positive-defect restriction belongs to the particular
logarithmic-time heat construction, not to the final basin inequality.

## 4. One vector at a fixed spectral cutoff gives the same full correction

Suppose S is symmetric and U is inverse-compatible. For the coefficient
connection on M_d define

    Delta_(rho,U)=(1/h)sum_s D_s*D_s,
    D_s(A)=rho(s)A-AU_s.

There is a fixed epsilon_*>0, depending only on the presentation and
Kazhdan data, such that

    min Spec Delta_(rho,U)<=epsilon_*^2

already implies the full linear correction (IR1). Neither a positive
count nor an operator-norm bound for the supplied eigenvector is
required. The exact irreducible target must still have dimension d.

Here is the Gram estimate that converts a spectral vector into the
coarse HS basin. Choose an eigenvector A with eigenvalue lambda<=epsilon^2
and normalize Tr(A*A)=d. Put H=A*A and X_s=A*rho(s)A. All traces and
HS norms in the next two identities are unnormalized. Symmetry gives
Delta A=2A-(2/h)sum_s rho(s)A U_s*. Taking its HS inner product
with AH and completing a square gives exactly

    lambda Tr(H^2)
      =(1/h)sum_s[Tr(H^2)-||X_s||HS^2
                         +||X_s-HU_s||HS^2].         (IR7)

The cross terms agree because
Re Tr(H X_s U_s*)=Re Tr(X_s* H U_s), by conjugation and cyclicity.
For Q=AA*, the pair-product identity is

    ||rho(s)Qrho(s)*-Q||HS^2
      =2[Tr(H^2)-||X_s||HS^2].

Drop the last squared norms in (IR7). Since Tr Q=d and rho is
irreducible, the Kazhdan bound for Ad(rho) yields

    Tr(H^2)-d <= (2h lambda/kappa^2)Tr(H^2).

For a=2h epsilon^2/kappa^2<1 it follows that

    ||H-I||_(2,d)^2<=a/(1-a).                         (IR8)

Complete the polar factor of A to a unitary V0. Equation (IR8) gives
||A-V0||_2<=sqrt(a/(1-a)). Its normalized coefficient energy is
h lambda, so

    max_s||U_s-V0* rho(s)V0||_2
       <=xi(epsilon),
    xi(epsilon)=sqrt(h)epsilon+2sqrt(a/(1-a)).         (IR9)

Choose epsilon_*>0 with a_*<1 and xi(epsilon_*)<=eta0. The exact
representation V0*rho V0 is again irreducible. Apply (IR1) in its
coarse basin to obtain a linear correction of U in the conjugacy
class of rho, with the same dimension-independent constant L.

Conversely, if e is the normalized generator distance of U to that
conjugacy class, testing the coefficient connection on a corresponding
unitary gives min Spec Delta_(rho,U)<=e^2. Thus a sufficiently small
fixed spectral basin and a sufficiently small fixed coarse orbit basin
imply each other, with the explicit change of radius in (IR9).

## 5. Rectangular targets of dimension at least the input

The fixed spectral basin extends to a supplied irreducible
rho:G->U(N) with N>=d. Suppose U acts on C^d and

    min Spec Delta_(rho,U)<=epsilon_*^2,              (IR10)

with the same fixed cutoff as in Section 4. Then there is an exact
representation sigma conjugate to rho, in a coordinate decomposition
C^N=C^d direct_sum C^(N-d), satisfying

    max_s||sigma(s)-(U_s direct_sum I_(N-d))||_(2,N)
       <=L delta(U) sqrt(d/N),
    (N-d)/d<=L^2 delta(U)^2/kappa^2.                  (IR11)

In particular this is a full flexible correction with linear error and
quadratic padding. No finite-image hypothesis is used. Moreover the
original rectangular connection has

    min Spec Delta_(rho,U)<=L^2 delta(U)^2.           (IR12)

To prove this, take a low-energy eigenvector A:C^d->C^N and normalize
Tr(AA*)=N. The weighted identity (IR7) is unchanged with H=A*A.
Irreducibility now makes the invariant projection of Q=AA* equal to
I_N, so the same argument gives, for a=2h epsilon_*^2/kappa^2<1,

    Tr(H^2)-N<=a Tr(H^2),
    ||AA*-I_N||HS^2<=aN/(1-a).

Since rank H<=d, Cauchy--Schwarz also gives

    N^2/d<=Tr(H^2)<=N/(1-a),
    N<=d/(1-a).                                      (IR13)

Pad A with N-d zero columns. Its target Gram AA* is unchanged, and
its residual against U direct_sum I_(N-d) has no new-column term,
because those columns of the padded map are zero. Complete its polar
factor to a unitary V0 on C^N. Normalizing by N, the same singular-value
and edge estimates as before put U direct_sum I_(N-d) within
xi(epsilon_*)<=eta0 of V0*rho V0.

Apply the same-dimensional HS-basin theorem in dimension N. Its input
defect is exactly delta(U)sqrt(d/N), proving the first line of (IR11).
To improve the coarse dimension bound (IR13), put q=N-d. If q>0,
N>=2 and the irreducible sigma has no invariant vector. Let J_q include
the added identity columns. Property (T) for left multiplication by
sigma on Hom(C^q,C^N) gives

    kappa sqrt(q)
      <=max_s||sigma(s)J_q-J_q||HS
      <=L delta(U)sqrt(d).

This proves the quadratic padding bound; if delta(U)=0 it forces q=0.
Finally, write sigma=V*rho V and let J_d include the original columns.
The isometry VJ_d has generator residual at most L delta(U)sqrt(d)
against rho and U. Its Rayleigh quotient is at most L^2 delta(U)^2,
proving (IR12). No assumption on the rank or operator norm of the
original eigenvector was required.

## 6. Why the irreducible hypothesis matters

The general heat-mass boundary allows a small fixed unmatched summand
inside a reducible comparison representation. Its invariant Gram can
then be far from a scalar, even after the coefficient energy becomes
zero. Here irreducibility forces every invariant Gram to be scalar;
positive retained mass consequently controls the whole input space.

This does not contradict the dilution boundary in
`heat-mass-loss-and-fixed-basin-boundary-2026-09-05.md`: the comparison
representation used by that argument is a large trivial direct sum,
which is reducible. Nor does this theorem supply an irreducible coarse
comparison or a fixed-cutoff vector for an arbitrary approximate tuple.
The same-dimension assumption is what removes padding altogether.
Section 5 handles larger irreducible targets by padding first and then
proves that the necessary padding is quadratic in the defining defect.
It does not assert the corresponding full correction for targets of
dimension smaller than the input.
