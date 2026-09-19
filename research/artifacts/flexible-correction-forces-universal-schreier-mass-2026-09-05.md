# Flexible correction forces full spectral mass at the universal host

Analytic necessity theorem, 2026-09-05. A known flexible exact correction
forces almost d low-energy dimensions in the fixed universal quotient
host. Together with the pair-product estimate below, it forces the full
spectral Gram matrix to converge to the identity. Thus full-space
normalization does not make the Schreier spectral gate unnecessarily
strong. This theorem does not construct a correction from arbitrary
small presentation defect.

## 1. Quantitative spectral mass from an exact correction

Let G=SL_5(Z), with finite symmetric generating set S, h=|S|, and
Kazhdan constant kappa. Let U_s in U(d) be inverse-compatible unitaries.
Suppose rho:G->U(D) is genuine, d<=D<=2d, and

    max_s ||rho(s)-(U_s direct_sum I_(D-d))||_(2,D) <= eta.

Use the fixed universal quotient

    Q=Q_(2d)=G/Gamma(lcm(1,...,floor((2d)^(1/3)))),
    Pi=lambda_Q.

The universal-level theorem in
`universal-dimension-schreier-host-2026-09-05.md` makes rho factor
through this quotient. On Hom(C^d,ell^2(Q)) define

    D_s(T)=Pi(s)T-TU_s,
    Delta=(1/h)sum_s D_s^*D_s,
    P_epsilon=1_[0,epsilon^2](Delta),  epsilon>0.

Then

    rank(P_epsilon) >= d-eta^2 D/epsilon^2.             (FN1)

Every HS norm inside this proof is unnormalized unless a dimension is
displayed. In particular, the numerator on the right is eta^2 D, and
not eta^2 times the quotient dimension.

Let J:C^d->C^D be the coordinate inclusion. The defect maps

    R_s=rho(s)J-JU_s

satisfy ||R_s||_HS^2<=eta^2 D. Choose an HS-orthonormal basis (T_a) of
the exact intertwiner space Hom_G(rho,Pi). The regular host gives

    dim Hom_G(rho,Pi)=D,
    sum_a T_a^*T_a=I_D.                                (FN2)

For verification, write rho=direct_sum_sigma sigma tensor I_(m_sigma),
with r_sigma=dim sigma. On the sigma block of the regular representation,
an orthonormal intertwiner basis is
r_sigma^(-1/2) I_(V_sigma) tensor |l><a|, with
1<=l<=r_sigma and 1<=a<=m_sigma. Summing their source Gram matrices
gives the identity, and counting them gives sum r_sigma m_sigma=D.

Put S_a=T_a J. As vectors in Hom(C^d,ell^2(Q)), these form a Bessel
family. Explicitly, restriction L(T)=TJ is a contraction between the
two rectangular HS spaces, and the frame operator is

    A=sum_a |S_a><S_a|=L P_exact L^*,  0<=A<=I.

Equation (FN2) gives

    Tr A=sum_a ||T_a J||_HS^2=d.

Exact intertwining yields D_s(S_a)=T_a R_s. Summing with (FN2) gives

    Tr(Delta A)
      =(1/h)sum_(s,a)||T_a R_s||_HS^2
      =(1/h)sum_s ||R_s||_HS^2
      <=eta^2 D.

Since Delta>=epsilon^2(I-P_epsilon),

    Tr(P_epsilon A)>=d-eta^2 D/epsilon^2.

Finally A<=I implies Tr(P_epsilon A)<=rank(P_epsilon), proving (FN1).
There is no need for the S_a to remain orthogonal after restriction.

## 2. The pair-product upper bound for a full spectral space

The pair-product calculation in
`spectral-pair-products-control-schreier-gram-2026-09-05.md`, recalled
and independently audited here, applies to any finite
regular quotient host and any inverse-compatible unitary tuple; it does
not assume an exact comparison or canonical limiting traces.

Let E=range P_epsilon be nonzero, with HS-orthonormal basis (V_a), and
put

    r=dim E,  b=r/d,
    B=sum_a V_a^*V_a,  H=B/b,
    alpha=2h epsilon^2/kappa^2 <1.

Then

    r <= Tr(B^2) <= r/(1-alpha),
    b <= 1/(1-alpha),
    tr_d(H^2) <= 1/(b(1-alpha)).                       (FN3)

Here are the trace identities underlying the bound. With
X_s=sum_a V_a^*Pi(s)V_a, expanding all pair products gives

    sum_(a,b)||Pi(s)V_a V_b^*Pi(s)^*-V_a V_b^*||_HS^2
      =2(Tr(B^2)-||X_s||_HS^2).

The full spectral projection commutes with the right regular Q-action.
Decompose it as direct_sum_sigma P_sigma tensor I_(r_sigma), with
mu_sigma=rank P_sigma. Choose the basis respecting this decomposition.
Index the basis in one block by (sigma,u,l), where u ranges over an
orthonormal basis of E_sigma and l over the regular multiplicity space.
Schur averaging of the pair indexed by (sigma,u,l) and (sigma,v,m) is
delta_(u,v) I_(V_sigma)/r_sigma tensor |l><m|; between inequivalent
sigma blocks it is zero. Consequently its total invariant squared HS
mass is sum r_sigma mu_sigma=r. Its total squared HS mass before
averaging is Tr(B^2).

For completeness, use the positive operator R_B(V)=VB on the
rectangular HS space. Since 0<=Delta P_epsilon<=epsilon^2 P_epsilon,

    Tr(R_B Delta P_epsilon)<=epsilon^2 Tr(B^2).

No commutation of R_B with Delta is assumed: positivity of both factors
in the difference suffices for the trace inequality. Expansion, using
inverse compatibility, identifies the left side as

    (1/h)sum_s [Tr(B^2)-||X_s||_HS^2
                         +||X_s-BU_s||_HS^2].

Each first difference is nonnegative by the pair-displacement identity.
Drop the final squared norms, and apply the Kazhdan inequality to the
genuine conjugation representation of Pi on the direct sum of all
pair-product HS spaces. This gives

    Tr(B^2)-r <=(2h epsilon^2/kappa^2) Tr(B^2).

The lower bound in (FN3) is orthogonality of invariant projection.
Also Tr B=r, so scalar Cauchy--Schwarz gives r^2/d<=Tr(B^2), proving
the remaining two bounds in (FN3).

## 3. Necessity along any flexibly correctable sequence

Suppose U_(j,s) admits flexible corrections rho_j with
D_j/d_j->1 and generator errors eta_j->0. For large j, D_j<=2d_j,
so use exactly Q_(2d_j) above. Choose positive cutoffs epsilon_j->0
with eta_j/epsilon_j->0; for example
epsilon_j=sqrt(eta_j+1/j).

Equations (FN1) and (FN3) give

    1-eta_j^2 D_j/(epsilon_j^2 d_j)
      <= b_j <=1/(1-2h epsilon_j^2/kappa^2).

Thus b_j->1, the low-energy spaces are eventually nonzero, and

    ||H_j-I||_(2,d_j)^2
      =tr_(d_j)(H_j^2)-1
      <=1/[b_j(1-2h epsilon_j^2/kappa^2)]-1
      ->0.                                            (FN4)

In particular their soft mass converges to one half:

    tr_(d_j)[H_j(H_j+I)^(-1)] ->1/2.

They also satisfy full soft coverage:

    lim_(tau down to 0) limsup_j
      tr_(d_j)[tau(H_j+tau I)^(-1)] =0.

For each fixed tau>0, the last trace tends to tau/(1+tau), by (FN4)
and the scalar Lipschitz bound on the positive half-line. The soft mass
claim follows by the same argument at tau=1.

No canonical-character hypothesis was needed for this necessity
direction. For canonical sequences, the earlier constructive frame
theorem supplies the converse. At the group level, existence of a
positive-density low-energy spectral space on a subsequence of every
canonical sequence is therefore an exact reformulation of the remaining
flexible-stability problem: (FN3) supplies a bounded second moment, the
positive-corner bootstrap supplies full stability, and (FN1) supplies
necessity at the fixed universal hosts. This equivalence does not prove
that low-energy spectral mass exists for arbitrary approximate tuples.
