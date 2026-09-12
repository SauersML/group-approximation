# Constructing Schreier frames from low-energy spectral coverage

Analytic construction, 2026-09-05. This proves a dimension-independent
frame construction from a precise spectral coverage hypothesis. It does
not prove that QRC curvature supplies that hypothesis.

## 1. Spectral data and the sufficient coverage condition

Let G=SL_5(Z), with finite symmetric Kazhdan set S, h=|S|, and constant
kappa in the convention used by MSC. Let Q_j be finite quotients of G;
one may choose the universal dimension-dependent congruence quotients in
`universal-dimension-schreier-host-2026-09-05.md`. Write
Pi_j=lambda_(Q_j) on K_j=ell^2(Q_j).

Let U_(j,s) be canonical asymptotic unitary representations on C^(d_j),
with U_(j,s^-1)=U_(j,s)^*. Thus normalized traces of evaluated fixed words
converge to the canonical trace of their evaluations in G. In particular
d_j tends to infinity. Define on Hom(C^(d_j),K_j), with unnormalized HS
inner product,

    D_s(T)=Pi_j(s)T-TU_(j,s),
    Delta_j=(1/h) sum_s D_s^*D_s,
    E_j=range 1_[0,epsilon_j^2](Delta_j),  epsilon_j -> 0.

Assume E_j is nonzero. For an HS-orthonormal basis (T_a) of E_j put

    r_j=dim E_j,                  b_j=r_j/d_j,
    B_j=sum_a T_a^*T_a,           C_j=sum_a T_a T_a^*,
    H_j=B_j/b_j,
    K_eff,j=Tr(C_j^2)/(b_j^2 d_j).                         (LF1)

These operators and numbers do not depend on the basis. The sufficient
coverage condition is

    lim_(tau down to 0) limsup_j
      tr_(d_j)[tau(H_j+tau I)^(-1)] = 0.                 (LF2)

This permits kernels of dimension o(d_j) and arbitrarily small singular
values on vanishing fractions of the input. It is strictly more suitable
than demanding a uniform positive least singular value.

Under (LF2), there are integers k_j=o(d_j) and maps

    J_j:C^(d_j) -> K_j tensor C^(k_j)

such that both their Gram defect and their Schreier edge error tend to
zero. Their coset coordinate maps are therefore MSC rectangular frames
with genuine trivial subgroup holonomy of dimension k_j. The construction
and every constant below are independent of |Q_j|.

## 2. Gaussian compression of a frame

First fix j and suppress subscripts. For any component maps S_a:C^d->K,
let F=col_a S_a, M=F^*F, and C'=sum_a S_a S_a^*. Choose independent
standard complex Gaussian scalars g_(la), and put

    J=k^(-1/2) col_(l=1,...,k)(sum_a g_(la) S_a).

The two complex Gaussian pairings give the exact identities

    E(J^*J)=M,
    E ||J^*J-M||_(2,d)^2 = Tr((C')^2)/(k d).            (LF3)

Indeed the second pairing in E Tr((T^*T)^2), for
T=sum_a g_a S_a, is sum_(a,b)Tr(S_a^*S_b S_b^*S_a)
=Tr((C')^2); the first pairing is Tr(M^2).

Write R_s(F)=Pi^direct_sum(s)F-FU_s. Gaussian second moments also give

    E sum_s ||(Pi(s) tensor I_k)J-JU_s||_HS^2/d
      =sum_s ||R_s(F)||_HS^2/d.                         (LF4)

Apply Markov's inequality with factor 4 separately to (LF3) and (LF4).
With probability at least one half both bounds hold. In that realization,

    ||J^*J-I||_(1,d)
      <= ||M-I||_(1,d)+2 sqrt(Tr((C')^2)/(k d)),
    max_s ||(Pi(s) tensor I_k)J-JU_s||_HS/sqrt(d)
      <= 2 sqrt(sum_s ||R_s(F)||_HS^2/d).               (LF5)

This is an existence proof by explicit sampling, not a computation on
the enormous quotient.

## 3. Soft polar normalization

Stack the spectral basis as F_0=b^(-1/2) col_a T_a, so F_0^*F_0=H and

    sum_s ||R_s(F_0)||_HS^2/d <= h epsilon^2.

For tau>0 define

    F_tau=F_0(H+tau I)^(-1/2),
    a(tau)=tr_d[tau(H+tau I)^(-1)].

Its Gram matrix is H(H+tau I)^(-1), and its Gram L1 defect is exactly
a(tau). The rectangular map

    Phi_tau(A)=A(A^*A+tau I)^(-1/2)

is equivariant under left and right unitaries and is HS Lipschitz with
constant at most sqrt(2/tau). For completeness, apply the scalar
Lipschitz bound for f(x)=x/sqrt(x^2+tau) to the Hermitian block matrices
[[0,A^*],[A,0]]. For Hermitian matrices, expansion in their two spectral
bases proves the HS Lipschitz bound directly from
|f(x)-f(y)|<=tau^(-1/2)|x-y|. The relevant off-diagonal block of f is
Phi_tau(A), giving the stated bound. Consequently

    sum_s ||R_s(F_tau)||_HS^2/d <= 2h epsilon^2/tau.

Writing F_tau=col_a S_a, its other covariance satisfies

    C_tau=sum_a S_a S_a^*
      =(1/b)sum_a T_a(H+tau I)^(-1)T_a^*
      <= C/(b tau),
    Tr(C_tau^2)/d <= K_eff/tau^2.

Thus Gaussian compression gives a frame with

    zeta <= a(tau)+2 sqrt(K_eff/(tau^2 k)),
    beta <= 2 sqrt(2h/tau) epsilon.                    (LF6)

For comparison, the stronger hypothesis B>=c b I permits exact whitening
F=(col_a T_a)B^(-1/2). In this case the sharper bounds are

    zeta <= 2 sqrt(K_eff/(c^2 k)),
    beta <= 2 sqrt(h/c) epsilon.                       (LF7)

Here the polar map is HS Lipschitz with constant 1/a when both inputs
have least singular value at least a: if A=UH and A'=VK with
H,K>=aI, expand Re Tr((U-V)^*(A-A')) and use I-Re(U^*V)>=0
to bound it below by a||U-V||_HS^2, then use Cauchy--Schwarz.
Apply this with a=sqrt(cb). Equation (LF7) is only a sufficient special
case; it is not proposed as a necessary coverage condition.

## 4. Effective covariance is automatically sublinear

For these full spectral subspaces, canonical asymptotics and a lower
bound b_j>=b_0>0 imply

    K_eff,j/d_j -> 0.                                  (LF8)

Here is a proof with no square-root operator inequality. Let P be the
projection onto E. The unitary
A_s(T)=Pi(s)T U_s^* obeys

    ||(A_s-I)P||_HS <= sqrt(h) epsilon sqrt(r).

Writing A_s P A_s^*-P as a sum of two products gives trace norm at most
2sqrt(h) epsilon r. Take the partial trace over the source space. Since
C is that partial trace of P,

    ||Pi(s)C Pi(s)^*-C||_1 <= 2sqrt(h) epsilon r.

Also 0<=C<=dI. Thus the selfadjoint difference on the left has operator
norm at most d, and its squared HS norm is at most
2sqrt(h) epsilon d r.

The spectral projection P commutes with the right regular Q-action,
so C lies in the left group algebra. Projecting C onto the invariants of
the genuine conjugation action of G gives its centralization C_0. The
Kazhdan estimate and orthogonality give

    Tr(C^2)=Tr(C_0^2)+||C-C_0||_HS^2,
    ||C-C_0||_HS^2 <= 2sqrt(h) epsilon d r/kappa^2.       (LF9)

Decompose the left regular representation as
direct_sum_sigma V_sigma tensor C^(r_sigma), r_sigma=dim sigma.
Right invariance gives P=direct_sum_sigma P_sigma tensor I_(r_sigma),
where P_sigma acts on V_sigma tensor conjugate(C^d). Set
mu_sigma=rank P_sigma. Then

    r=sum_sigma r_sigma mu_sigma,
    C_0|sigma=(mu_sigma/r_sigma) I_(r_sigma^2),
    K_eff/d <= sum_sigma mu_sigma^2/(b^2d^2)
               +2sqrt(h) epsilon/(kappa^2 b).           (LF10)

For every fixed irreducible G-representation sigma, mu_(j,sigma)/d_j
tends to zero (set it to zero if sigma does not factor through Q_j).
To verify this without assuming U_j genuine, let Delta_(j,sigma) be the
corresponding connection block and L_(j,sigma)=I-Delta_(j,sigma)/4.
This is a positive contraction, and on the low-energy block it is at
least 1-epsilon_j^2/4. For every fixed positive integer a,

    mu_(j,sigma)/(r_sigma d_j)
      <= (1-epsilon_j^2/4)^(-a) tr(L_(j,sigma)^a).

The right-hand trace is normalized by r_sigma d_j. Its finite word
expansion converges, by canonical asymptotics, to the canonical trace
of the corresponding lazy regular averaging operator to power a.
Kazhdan's inequality bounds this limit by
(1-kappa^2/(4h))^a, since the regular representation of the infinite
group has no invariants. First take j to infinity and then a to infinity.

The universal-level theorem proves there are only finitely many
irreducible G-representations below any fixed dimension M. Their total
contribution to the sum in (LF10) therefore vanishes when b>=b_0.
For the remaining terms,

    sum_(r_sigma>=M) mu_sigma^2/(b^2d^2) <= 1/M^2,

because sum r_sigma mu_sigma=bd. This proves (LF8).

In the exact case U=rho factoring through Q, the zero-energy space has
B=I, b=1, C|sigma=(m_sigma/r_sigma)I_(r_sigma^2), and
K_eff=sum m_sigma^2/d<=k_min(rho). Thus (LF8) agrees with the exact
sublinear-seed theorem, while its proof here applies to approximate input.

## 5. Choosing the cutoff, regularization, and seed

Right invariance also gives rank B<=rank E=r. Indeed, on the conjugate
source space,
overline(B)=sum_sigma r_sigma Tr_(V_sigma)(P_sigma), and the rank of each
partial trace is at most r_sigma mu_sigma. Complex conjugation preserves
rank, so a(tau)>=1-b whenever b<1.
Condition (LF2) forces liminf b_j>=1, supplying the positive lower bound
needed for (LF8). It does not force every b_j to be at least one.

Using (LF2), (LF8), and epsilon_j->0, choose tau_j down to zero slowly
enough that simultaneously

    a_j(tau_j)->0,
    epsilon_j^2/tau_j->0,
    K_eff,j/(tau_j^2 d_j)->0.

This is an ordinary diagonal choice: for each fixed positive tau the
last two limits vanish, while the limsup of the first quantity can be
made arbitrarily small by choosing tau sufficiently small. Choose

    k_j=ceil sqrt(d_j max(1,K_eff,j/tau_j^2)).

Then k_j/d_j->0 and K_eff,j/(tau_j^2 k_j)->0. Equation (LF6) proves
zeta_j,beta_j->0. The ambient capacity is eventually adequate too:
Cauchy--Schwarz gives K_eff>=d/|Q|, so k|Q|/d>=k/K_eff tends to
infinity for this choice. The global polar and original-rank Kazhdan
argument of MSC therefore apply with gamma=beta+2sqrt(zeta).

## 6. The remaining input is spectral coverage

Low energy alone does not imply (LF2). For this example choose the
standard elementary-generator Kazhdan set and an exact canonical quotient
sequence rho_j of dimension n_j. Form the tuple

    U_(j,s)=rho_j(s) direct_sum exp(i t_j x_s)rho_j(s),
    t_j->0,  d_j=2n_j.

Choose real x_s with x_(s^-1)=-x_s and with nonzero exponent sum c on
some defining relator. Such a choice exists for a finite presentation of
the perfect group SL_5(Z). Choose t_j with exp(i t_j c)!=1. This tuple
is canonically asymptotic and is already o(1) from an exact tuple.
But its phase-twisted half has no exact intertwiner into a genuine
representation: applying that relator to an intertwiner gives
T=exp(i t_j c)T.

In a universal host containing rho_j, the zero-energy subspace therefore
has B equal to the projection onto the first half, b=1/2, H=2B, and
a_j(tau)>=1/2 for every tau. One can equally choose strictly positive
cutoffs below the smallest positive eigenvalue, with epsilon_j->0.
No stacking of these low-energy maps covers the missing half.

This example rules out automatically choosing the kernel or an
arbitrarily aggressive spectral cutoff. It does not rule out a suitable
larger cutoff. Nor should one demand uniformly invertible Gram matrices:
an o(d) hard-defect summand can be missed while costing only o(1) in
normalized HS distance. Condition (LF2) is designed to allow that case.
The unproved arithmetic step is the existence of cutoffs epsilon_j->0
whose full spectral spaces satisfy (LF2) for arbitrary canonical
approximate tuples. QRC does not presently establish that step.
