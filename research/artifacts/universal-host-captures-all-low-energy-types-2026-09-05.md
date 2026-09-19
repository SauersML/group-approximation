# One universal host captures every low-energy finite-dimensional type

For SL_5(Z), changing finite quotient hosts cannot uncover further
low-energy types after a single dimension-dependent universal host has
been used. This holds for arbitrary inverse-compatible unitary tuples,
without assuming small relator defects or canonical traces.

Fix a finite symmetric Kazhdan generating set S, h=|S|, and constant
kappa in the MSC convention. Let U_s in U(d), U_(s^-1)=U_s^*.
For any finite quotient Q of G=SL_5(Z), define

    Delta_(Q,U)=(1/h)sum_s D_s^*D_s,
    D_s(T)=lambda_Q(s)T-TU_s,
    E_Q=range 1_[0,epsilon^2](Delta_(Q,U)),
    r_Q=dim E_Q,
    B_Q=sum_(a in an HS-orthonormal basis of E_Q) T_a^*T_a.

Set a=2h epsilon^2/kappa^2. If a<1, put

    M=floor(d/(1-a)),
    Q_univ=Q_M
      =G/Gamma(lcm(1,...,floor(M^(1/3)))).

Then every finite quotient Q satisfies

    r_Q <= r_(Q_univ),
    0 <= B_Q <= B_(Q_univ).                            (HU1)

Every irreducible type having a nonzero low-energy block in any finite
quotient occurs in Q_univ. Conversely each active type of Q_univ is
already such a finite-quotient type. If a<=1/2, the fixed host Q_(2d)
may be used in place of Q_M for all those cutoffs simultaneously.

## Proof and exact block identities

For an irreducible G-representation sigma factoring through Q, let
m_sigma=dim sigma and define its connection block on
Hom(C^d,V_sigma) by

    Delta_(sigma,U)=(1/h)sum_s
      (T -> sigma(s)T-TU_s)^*(T -> sigma(s)T-TU_s).

Write E_sigma for its spectral space below epsilon^2, and
mu_sigma=dim E_sigma. These data depend only on the equivalence class
of sigma and on U, not on the quotient in which sigma is realized.
The right regular decomposition gives

    E_Q=direct_sum_(sigma in Irr(Q)) E_sigma tensor C^(m_sigma),
    r_Q=sum_(sigma in Irr(Q)) m_sigma mu_sigma,
    B_Q=sum_(sigma in Irr(Q)) B_sigma,
    B_sigma=m_sigma sum_(u=1,...,mu_sigma) A_(sigma,u)^*A_(sigma,u),
                                                               (HU2)

where the A_(sigma,u) form an HS-orthonormal basis of E_sigma. Each
B_sigma is positive and is unaffected by changing this basis or by
unitarily identifying two realizations of sigma.

If r_Q>0, the spectral pair-product theorem MSC14 gives

    r_Q<=d/(1-a).

Therefore any active sigma in Q has
m_sigma<=m_sigma mu_sigma<=r_Q<=M. The universal exact-representation
theorem MSC9 makes every such sigma factor through Q_M. Equation (HU2)
now proves both the count inequality and the positive-semidefinite
source-Gram inequality in (HU1), term by term. If r_Q=0, both are
immediate.

Equality holds in both formulas whenever Q contains every active type
of Q_univ. In particular, every finite quotient refining Q_univ has
exactly the same count and source Gram at this cutoff: its additional
irreducibles have zero low-energy blocks. This is an exact assertion,
not a comparison that loses a factor from either quotient's order.

## A dimension-dependent gap excludes large irreducible types

Every finite-dimensional unitary representation of SL_5(Z) has finite
image by MSC9. Let sigma be irreducible of dimension m>d, and let
lambda_min be the lowest eigenvalue of Delta_(sigma,U). Then

    lambda_min >= (kappa^2/(2h))(1-d/m).                (HU3)

If lambda_min>=kappa^2/(2h), the bound is immediate. Otherwise put
epsilon^2=lambda_min and realize sigma in the regular representation
of its finite image quotient. Its low-energy spectral space has count
at least m. MSC14 gives

    m <= d/(1-2h lambda_min/kappa^2),

which rearranges to (HU3). Thus all types of dimension greater than 2d
are excluded whenever a<=1/2. The host universality theorem removes a
genuine search parameter; it does not produce any active type or a
positive normalized count in the universal host.

The two inputs are the exact universal-level theorem and the spectral
pair-product theorem, recorded respectively in
`universal-dimension-schreier-host-2026-09-05.md` and
`spectral-pair-products-control-schreier-gram-2026-09-05.md`.

## Perturbing the tuple without a quotient-size loss

Use the same universal host Q_(2d) for two inverse-compatible tuples U
and V in U(d). Write N_U(t) for the count below t^2 in that host. Put

    eta=max_s ||U_s-V_s||_(2,d),
    r=N_V(epsilon),
    a=2h epsilon^2/kappa^2 <= 1/2,
    xi=sqrt(h) epsilon+2 sqrt(a/(1-a)).

For every t>0,

    N_U(t) >= min(r,d)
      - (xi sqrt(r)+eta sqrt(d))^2/t^2.                 (HU4)

For r=0 this is immediate. Otherwise the deterministic polar part of
MSC14 gives an exact representation Theta on C^r and a contraction
C:C^d->C^r with

    Tr(C^*C)=min(r,d),
    max_s ||Theta(s)C-CV_s||_HS <= xi sqrt(r).

When r<=d, C is the polar coisometry. When r>d, it is the restriction
to the original d columns of the padded polar unitary. In both cases
r<=2d, so Theta factors through Q_(2d).

Choose an HS-orthonormal basis T_a of the exact intertwiner space
Hom_G(Theta,lambda_(Q_(2d))). Regular multiplicities give

    sum_a T_a^*T_a=I_r.

On Hom(C^d,l2(Q_(2d))) form

    A=sum_a |T_a C><T_a C|.

Right multiplication by C is a contraction, hence 0<=A<=I. Also
Tr A=min(r,d), and the intertwiner identity gives

    Tr(Delta_U A)
      =(1/h)sum_s ||Theta(s)C-CU_s||_HS^2
      <=(xi sqrt(r)+eta sqrt(d))^2.

If P=1_[0,t^2](Delta_U), positivity and the spectral theorem imply
Tr((I-P)A)<=Tr(Delta_U A)/t^2. Since Tr(PA)<=rank P, this proves
(HU4). No quotient order enters either normalization or bound.

In particular, suppose d=d_j, ||U_j-V_j||_(2,d_j)->0, and epsilon_j->0.
Choose t_j->0 sufficiently slowly that
(xi(epsilon_j)+eta_j)/t_j->0. Since r_j/d_j<=1/(1-a_j), (HU4) yields

    N_(U_j)(t_j)/d_j
      >= min(N_(V_j)(epsilon_j)/d_j,1)-o(1).           (HU5)

Thus vanishing normalized spectral mass at all vanishing cutoffs is
invariant under an o(1) normalized-HS change of tuple. The reverse
implication follows by interchanging U and V. This conclusion concerns
vanishing cutoffs; it does not assert invariance of the count at one
fixed positive cutoff.
