# Every small irreducible compression has quadratic defect scale

Date: 2026-09-05. Analytic proof; no computation or builds.

Let G=<S|R> be a fixed finitely presented Kazhdan group. There are
theta_0,c,C>0 such that compressing any finite-dimensional irreducible
unitary representation rho:G->U(N) by k dimensions, where
0<k/(N-k)<=theta_0, and polar-rounding the generators gives defining
normalized-HS defect delta satisfying

    c k/(N-k) <= delta^2 <= C k/(N-k).                         (GC1)

The constants are independent of the representation, the removed subspace,
and the polar completions. This holds for infinite-image irreducibles as
well as finite-image ones. No H^2 vanishing is assumed.

In SL5 the same proof supplies the linear MSC19 first-vector estimate for
these compressed tuples. The active irreducible type is the original rho;
its regular multiplicity forces recovery of all N dimensions in the
corresponding low-energy target. This is a test class with a supplied
exact ambient representation, not a construction of an ambient for
arbitrary approximate tuples.

## 1. Compression data and constants

Write h=|S|, let ell be the longest defining-relator length, and fix a
Kazhdan constant kappa with

    dist(v,H^G)<=kappa^{-1} max_s ||pi(s)v-v||.

Use inverse-compatible tuples; if symmetric generator labels are separate
cochain coordinates, the presentation includes inverse-consistency rows.
Let W:C^d->C^N be the remaining-space inclusion, where d=N-k. Put
B_s=W* rho(s)W, and choose any unitary polar completions U_s consistently
on inverse letters. The standard singular-value computation gives

    ||rho(s)W-WU_s||HS^2 <= 2k,
    rank(rho(s)W-WU_s)<=k.                                   (GC2)

Indeed I-B_s*B_s has rank at most k, so all but k singular values c_i
equal one, and the squared edge error is 2 sum_i(1-c_i). Telescoping
defining words gives

    delta^2 <= 2ell^2 k/d.                                   (GC3)

Take mu,C_H,delta_H from the curved Hodge theorem, and write

    K0=|R|+4C_H,
    theta_0=min(1/2,mu/(8h),kappa^2/4),
    B0=2h theta_0+K0/mu.                                     (GC4)

All these constants depend only on the fixed group, presentation and
Kazhdan set. We initially assume k/d<=theta_0 and delta sufficiently
small; Section 4 removes the separate small-defect hypothesis.

If k>0, delta cannot equal zero in this range. Otherwise U is a genuine
d-dimensional representation and the exact coefficient action
X -> rho(g)X U(g)* has no invariant vector, because rho is irreducible
of dimension N>d. Applying property (T) to W and (GC2) gives
kappa^2 d<=2k, contrary to k/d<=theta_0<=kappa^2/4.

## 2. Heat improves the supplied inclusion

On Hom(C^d,C^N) use the coefficient operators
T_s(A)=rho(s) A U_s*. Normalize HS norms by sqrt(d). Let

    L0=sum_s(2I-T_s-T_s*),
    A_t=exp(-t L0)W,
    E(t)=sum_s ||rho(s)A_t-A_t U_s||HS^2/d,
    N(t)=||A_t||HS^2/d.

The initial map W is an operator contraction, N(0)=1, and
E(0)<=2h k/d<=2h theta_0. The curved Hodge heat estimates give

    ||A_t||op<=1,
    E(t)<=2h theta_0 exp(-2mu t)+(K0/mu)delta^2,
    N(t)>=1-2h theta_0/mu-(2K0/mu)delta^2 t.                   (GC5)

Choose delta_1 in (0,min(delta_H,e^{-1})) so that

    (2K0/mu^2)delta^2 log(1/delta)<=1/4
                  whenever 0<delta<delta_1.

At t=log(1/delta)/mu, (GC4)--(GC5) imply

    ||A_t||op<=1,
    ||A_t||HS^2>=d/2,
    sum_s ||rho(s)A_t-A_t U_s||HS^2<=B0 delta^2 d.             (GC6)

This estimate uses actual defining-relator defect delta, not the original
compression distance sqrt(k/d). Only property (T), through the curved
degree-one Hodge theorem, is needed.

## 3. Irreducible Schur variance forces the missing-rank bound

Put A=A_t and Q=AA*. For each generator, the operator contraction bound
and a two-term product expansion give

    ||rho(s)Q rho(s)*-Q||HS
       <=2||rho(s)A-AU_s||HS.

The invariant matrices for Ad(rho) are scalar by irreducibility, and
orthogonal projection onto them is Q -> (Tr Q/N)I_N. Thus property (T)
and (GC6) imply

    ||Q-(Tr Q/N)I_N||HS^2
       <=(4/kappa^2) max_s||rho(s)A-AU_s||HS^2
       <=(4B0/kappa^2)delta^2 d.                             (GC7)

On the other hand, Q is positive, rank Q<=d, and Tr Q>=d/2.
Cauchy--Schwarz on its at most d nonzero eigenvalues gives

    ||Q-(Tr Q/N)I_N||HS^2
       =Tr Q^2-(Tr Q)^2/N
       >=(Tr Q)^2(1/d-1/N)
       >=d k/(4N).                                          (GC8)

Combining (GC7)--(GC8) proves the explicit bounds

    k/N <=(16B0/kappa^2)delta^2,
    k/d <=[16(1+theta_0)B0/kappa^2]delta^2.                   (GC9)

The proof never passes to a finite quotient and needs no bound on the
image of rho. This is the general small-deletion defect floor missing
from the previous compression audit.

## 4. Uniform statement and asymptotic consequences

For delta>=delta_1, the trivial bound k/d<=theta_0 gives
k/d<=(theta_0/delta_1^2)delta^2. Therefore, with

    C_comp=max(16(1+theta_0)B0/kappa^2,theta_0/delta_1^2),

every compression with 0<k/d<=theta_0 satisfies

    (1/C_comp)k/d <=delta^2<=2ell^2 k/d.                       (GC10)

This proves (GC1) with no extra defect condition. For any sequence
k=o(N) with k>0, these bounds hold eventually and show d delta^2
comparable to k, including growing k. In particular k=1 yields the
formerly all-H^2 rank-integrality conclusion under property (T) and
finite presentation alone.

The existing rectangular Kazhdan comparison still shows that every
exact correction of vanishing error must eventually restore all k
deleted dimensions: dimensions d<=D<N have error at least
kappa-sqrt(6k/d). Thus the necessary padding k/d is comparable to
delta^2 for the whole compression family. Restoring rho gives sufficient
error at most sqrt(6k/N)=O(delta), and relative padding k/d=O(delta^2).
These upper bounds use the supplied ambient rho explicitly.

## 5. The universal-host first vector for SL5

For G=SL5, N=(1+k/d)d<2d in the range above, so rho factors through
the universal quotient Q_(2d). Equation (GC6) gives Rayleigh quotient
for Delta=L0/h at most

    L^2 delta^2,       L^2=2B0/h.                             (GC11)

Therefore MSC19 holds uniformly on this class of compressed irreducible
tuples. Every nonzero coefficient map here has target rho, and rho is
irreducible. A low-energy vector thus makes rho an active type in the
universal regular host. Its multiplicity there is N, so the complete
low-energy space at cutoff L delta has dimension at least N.

MSC14 supplies the alternate arithmetic proof of the missing-rank bound:
with a=2hL^2 delta^2/kappa^2<=1/2,

    N <= rank 1_[0,L^2 delta^2](Delta_(Q_(2d),U)) <= d/(1-a),
    k/d <=a/(1-a) <=(4hL^2/kappa^2)delta^2.                   (GC12)

The direct Schur proof is more general; (GC12) identifies the exact
spectral mechanism in the arithmetic program. Compressed irreducibles
do not refute MSC19. They are now a class for which its desired rate,
the full recovered target size, and the sharp quadratic padding scale
are all controlled.

No conclusion about arbitrary nearby tuples having a full linear
correction follows from this argument. It improves one supplied
inclusion into an irreducible exact ambient and then uses that ambient's
Schur structure. The first global seed for an arbitrary maximal residual
remains missing.
