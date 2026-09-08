# Independent audit of the primary congruence sector argument

2026-09-08. This audits the proposed Kirillov/conductor argument against
the primary orbit-method source and supplies its limiting-measure steps.
It concerns genuine congruence representations of SL_3(Z); it does not
exactify arbitrary lattice microstates or establish a nonhyperlinear
group.

## 1. Exact hypotheses and the intertwiner

Fix ANY prime p. Put

    C=SL_3(Z), K=SL_3(Z_p), h=diag(p,1,p^(-1)),
    D=C intersection h^(-1) C h,
    D_p=K intersection h^(-1) K h.

Let sigma_n:C->U(d_n) be genuine representations factoring through
SL_3(Z/(p^(a_n)m_n)), with gcd(m_n,p)=1. Let H_n be unitary matrices
such that

    ||H_n sigma_n(d)-sigma_n(hdh^(-1))H_n||_2 ->0

on a fixed finite generating set of D. Both sides define genuine
D-representations. Since D is finite index in the Kazhdan group C,
orthogonal projection on their intertwiner space gives contractions
T_n satisfying

    T_n sigma_n(d)=sigma_n(hdh^(-1))T_n   for every d in D,
    ||T_n-H_n||_2 ->0.                                (1)

Contraction follows by averaging the unitary action
X -> sigma_n(hdh^(-1)) X sigma_n(d)^*. The polar partial isometry of
T_n intertwines the same representations. Its initial and final
supports give a common subrepresentation of dimension at least

    (1-||T_n-H_n||_2^2)d_n.                            (2)

Indeed the squared distance of a unitary from an operator of rank r
is at least 1-r/d_n. The supports may have larger dimension than the
lower bound; no lower singular-value assumption is necessary.

Chinese remaindering gives commuting p-primary and coprime factors
of sigma_n. Write sigma_(n,p):K->U(d_n) for the first factor. For any
k in D_p, use surjectivity of reduction of SL_3(Z) modulo p^b m_n
and the Chinese remainder theorem to choose d in C with

    d=k modulo p^b,      d=1 modulo m_n,      b>=a_n+2.

The extra two p-adic digits are essential here: conjugation by h can
divide an entry by p^2. Thus d and hdh^(-1) agree with k and
hkh^(-1), respectively, modulo p^(a_n). Moreover b>=2 ensures d
belongs to D, since the defining integrality conditions for hdh^(-1)
are conditions modulo p^2. Both coprime components are the identity,
because h is invertible modulo m_n. This also covers a_n<2. Merely
choosing b>=max(a_n,2) would establish membership in D but would not
in general control the conjugated reduction to the required precision.

Consequently (1) holds for the p-primary pair alone:

    T_n sigma_(n,p)(k)
       =sigma_(n,p)(hkh^(-1))T_n       for every k in D_p.       (3)

Every value in (3) is a value in a finite quotient, so density plus
continuity, or the finite quotient surjectivity just proved, justifies
the passage from D. In particular

    sup_(k in D_p)||H_n sigma_(n,p)(k)H_n^*
                        -sigma_(n,p)(hkh^(-1))||_2 ->0.        (4)

This uniform statement, not merely convergence at fixed k, is what
authenticates the later Fourier-measure comparison.

## 2. The primary source and the prime 2

The source checked directly is Boyarchenko--Sabitova, *The orbit
method for profinite groups and a p-adic analogue of Brown's theorem*,
[arXiv:math/0608126](https://arxiv.org/pdf/math/0608126).
Theorem 2.6, printed page 12, applies to every uniform pro-p group
for p>=3. It does not require p to exceed the group's dimension.
If P=exp(l) and an irreducible representation corresponds to a finite
coadjoint orbit O in l^vee, its normalized character is

    chi(exp X)/chi(1)=|O|^(-1)sum_(lambda in O)lambda(X).        (5)

At p=2 one must not quote (5) on all of P. Theorem 2.8, printed page
14, instead says that each irreducible character restricted to P^2
is a multiple of the inverse Fourier transform of an orbit in
(2l)^vee. Evaluating at the identity fixes the multiple, so its
NORMALIZED restriction has exactly the positive probability-measure
formula (5) for X in 2l, with O in (2l)^vee. Several irreducibles
can give the same measure. Injectivity is not needed below.

Take P=K_r, the principal congruence group, with r>=1 for odd p and
r>=2 for p=2. Its Lie lattice is l_r=p^r sl_3(Z_p). It is uniform:
the commutator lattice lies in p l_r for odd p and in 4 l_r at 2.
Set alpha=1 for odd p and alpha=2 for p=2. Equations (5) and its
prime-2 version assign to every finite-dimensional P-representation
a probability measure on (alpha l_r)^vee whose Fourier transform is
the normalized character evaluated on exp(alpha l_r).

This assignment is affine for direct sums weighted by normalized
dimension. If two P-representations on equal total dimension have a
common subrepresentation of relative dimension at least 1-delta,
their measures have total variation distance at most delta, with
TV(mu,nu)=sup_E|mu(E)-nu(E)|. In fact their common representation
supplies a common positive measure of mass at least 1-delta. The
prime-2 noninjectivity causes no problem for this implication.

All logarithms, exponentials, and conjugations here are exact. No
truncated Baker--Campbell--Hausdorff formula is used and no error is
multiplied by the representation's conductor.

## 3. Restriction gives exact covariance modulo one compact lattice

Let V be the Q_p-linear dual of sl_3(Q_p). Fix a nontrivial additive
character of Q_p. Write L=alpha l_r and B=L^perp<=V. Thus
L^vee=V/B, where B is a compact open lattice. Let mu_n be the positive
Fourier measure of sigma_(n,p)|P on V/B given above.

It is K-invariant. Indeed the normalized character is invariant under
conjugation by K; logarithm intertwines that action with its linear
adjoint action, and uniqueness of Fourier transforms identifies the
transformed probability measures. This argument works also at p=2.

Choose s>=r+2 and Q=K_s. Then hQh^(-1)<=P and Q<=D_p. Put
L'=alpha l_s and B'=(L')^perp. Equation (2), restricted through (3),
supplies common Q-subrepresentation mass 1-o(1) for

    sigma_(n,p)|Q,      k -> sigma_(n,p)(hkh^(-1))|Q.

Apply the affine Fourier assignment for Q (on Q^2 when p=2).
The two resulting measures on V/B' have TV distance o(1). By direct
evaluation of their Fourier transforms, they are precisely

    (restriction L to L')_* mu_n,
    (lambda -> lambda composed with Ad(h)|L')_* mu_n.           (6)

This uses Ad(h)L'<=L, which follows from s>=r+2. It does not need an
orbit-theoretic rule for restricting irreducible representations;
Fourier uniqueness supplies the equality for reducible restrictions.

Fatten each atom of mu_n by normalized Haar measure on its coset of
B. The result is a K-invariant probability measure nu_n on V. If
A=Ad(h)^* denotes the corresponding linear dual map, (6) says that
the images of nu_n and A_*nu_n in V/B' differ in TV by o(1).

## 4. Escape would give an invariant measure on projective space

Use the compactification of V obtained by embedding v as [v:1] in
P(V direct_sum Q_p). Its boundary is P(V), and every invertible
linear map of V extends continuously to this compactification.

The quotient-TV conclusion has a useful exact interpretation. After
discarding a probability o(1), one can couple X_n with law nu_n and
Y_n with law A_*nu_n so that

    X_n-Y_n belongs to B'.                            (7)

First couple the quotient laws to agree with maximal probability,
then use conditional measures on their cosets. The compact lattice
B' is fixed independently of n.

Pass to a convergent subsequence of the joint laws in the product of
the two compactifications. If v_j-w_j remains in a fixed compact
subset of V and v_j tends to [v:0], then w_j tends to the same
[v:0]. This follows immediately after scaling their homogeneous
coordinates so that the largest coordinate has norm one. Therefore
the limiting coupling is supported on the diagonal whenever either
coordinate is on the boundary. The boundary parts of any weak limit
of nu_n and A_*nu_n are identical.

It follows that the boundary part beta of a weak limit of nu_n is
A-invariant. It is also K-invariant by the exact K-invariance of nu_n.
If the sequence nu_n were not uniformly tight, diagonal selection of
an escaping positive mass would give beta(P(V))>0.

There is no such nonzero finite K- and A-invariant measure. Here is
an elementary proof which avoids an additional projective-measure
theorem. The group generated by K and h is SL_3(Q_p): elementary
root subgroups over Z_p and conjugation by powers of h supply all
root parameters in Q_p, after Weyl conjugation. Under the adjoint
representation, choose one diagonal element with eigenvalues of
distinct absolute value on the six root spaces and on the Cartan
weight space; for example diag(p,p^3,p^(-4)) has root exponents
plus or minus 2, 5, 7 and Cartan exponent zero. It belongs to the
group generated by K and h.

The recurrent projective points of this element lie in the union of
the projectivizations of its seven proper weight spaces. A vector
with components of two different absolute-value weights converges
projectively to its highest-weight component and cannot recur to its
original projective point. Poincare recurrence therefore forces any
invariant probability to be supported on this finite union.

The support is also K-invariant. The K-orbit of any point in it
would thus lie in that finite union of proper linear subspaces. The
group K is Zariski dense in SL_3 over Q_p, and the algebraic orbit
closure is irreducible. It would have to lie in one of these proper
subspaces. This is impossible because the adjoint representation of
SL_3 over the characteristic-zero field Q_p is irreducible: the
linear span of a nonzero orbit is the whole adjoint module. The
dual representation has the same property. Thus beta=0.

This proves uniform tightness of nu_n. There is no requirement that
all mass escape or that the conductor distribution be concentrated
at one depth.

## 5. Tightness kills the p-primary factor

Tightness has the concrete implication

    lim_(m->infinity) limsup_n
      sup_(k in K_m)||sigma_(n,p)(k)-1||_2=0.          (8)

To see this, choose a compact frequency set carrying mass at least
1-epsilon for every sufficiently large n. A sufficiently deep Lie
lattice l_m annihilates this set. The exact Fourier formula then
gives Re tr(sigma_(n,p)(exp X))>=1-2epsilon uniformly for X in l_m,
so the squared distance to 1 is at most 4epsilon. This works on the
extra deep subgroup used at p=2 as well.

For every x in Z_p the upper root x_12(x) belongs to D_p, and

    h x_12(x) h^(-1)=x_12(px).

Write epsilon_n for the uniform error in (4). For each fixed j,

    ||sigma_(n,p)(x_12(1))-1||_2
      <=||sigma_(n,p)(x_12(p^j))-1||_2+j epsilon_n.    (9)

First take limsup in n, then let j tend to infinity. Equation (8)
makes the right side zero. Exact Weyl conjugation gives the same
conclusion for all elementary generators of C.

Finally apply the fixed Kazhdan estimate for C to its genuine
representation by LEFT multiplication through sigma_(n,p) on M_d,
with unit vector I in normalized Hilbert--Schmidt norm. The invariant
projection of I is the projection P_n onto the invariant subspace
of sigma_(n,p). Therefore

    1-tr(P_n)
      <=kappa^(-2)max_(c in S)
                       ||sigma_(n,p)(c)-1||_2^2 ->0.           (10)

Thus the total normalized dimension of the nontrivial p-primary
part tends to zero. The argument gives this mass conclusion, not
merely pointwise collapse of a few roots.

## 6. Scope of the audited conclusion

The argument establishes primary-mass vanishing for every prime p
under the exact congruence representation and approximate fixed-D
intertwining hypotheses of Section 1. No regular limiting character,
Plancherel multiplicities, conductor bound, flatness, or finite-field
character-ratio estimate is used. At p=2 the restriction-to-squares
theorem must be retained explicitly at both Fourier assignments.

This closes the primary part of the lattice-exact arithmetic sector.
It does not make arbitrary approximate C representations exact.
In particular, replacing the genuine sigma_n in (1) by arbitrary
unitary microstates would invalidate the first use of property (T)
and the finite-dimensional character decompositions. That remains
the separate difficulty toward the headline nonhyperlinear target.

## 7. Independent review of the finite tracial coordinate extension

The complete sibling proof is in
`sl3-primary-exact-sector-kirillov-tightness-2026-09-08.md`. Its extension
from matrices to arbitrary finite tracial von Neumann algebras checks,
provided each lattice representation genuinely factors through a finite
congruence quotient. Here are the points which replace dimension counts.

Let sigma:C->U(M) have finite congruence image and let tau be the
normalized finite trace. The two overlap representations have finite
joint image, so their invariant projection on L^2(M,tau) is a finite
average. Consequently the projected intertwiner T belongs to M, is a
contraction, and has polar partial isometry v in M. Write e=v^*v and
f=vv^*. Then e and f belong to the appropriate representation commutants,
tau(e)=tau(f), and

    tau(1-e) <= ||T-H||_2^2.

After the CRT restriction, write rho_1(k)=rho(k) and
rho_2(k)=rho(hkh^(-1)) for k in Q. The intertwining equation gives

    tau(e rho_1(k)) = tau(f rho_2(k)).

Indeed v rho_1(k)=rho_2(k)v, and traciality equates the trace of
v rho_1(k)v^* with that of e rho_1(k). Each side is a positive
central character of mass tau(e), since e and f commute with their
respective representations. The complementary corners give positive
characters of mass 1-tau(e).

The algebra generated by any finite group image is finite dimensional,
even when M is not. A positive tracial functional on that algebra is a
positive real weighted sum of normalized irreducible characters. Apply
the affine Kirillov assignment to the common corner and the two
complementary corners. The Fourier measures therefore share a positive
measure of mass tau(e); their variation norm is at most 2(1-tau(e)).
This justifies the total-variation comparison without choosing integral
multiplicities or assuming that M is a factor.

The final property (T) argument also survives. The finite average
P=|F|^(-1)sum_(g in F)rho(g) lies in M and is a projection. Left
multiplication by P is the orthogonal projection onto invariant vectors
in L^2(M,tau), so the projection of the vector 1 is P and its squared
distance is 1-tau(P). Since (rho(k)-1)P=0 for every k, the concluding
bound is

    sup_(k in K)||rho(k)-1||_2 <= 2 sqrt(1-tau(P)).

The sibling proof's compactification argument also checks: translations
by the fixed annihilator lattice act continuously on the projective
compactification and fix the boundary pointwise. Convolution with its
Haar probability therefore preserves every boundary restriction. Its
five-weight recurrence argument can use h itself; the extra diagonal
element used in Section 4 above is unnecessary.

## 8. What changes relative to the existing arithmetic lane

The established claim
`p-divisible-lambda-exact-mass-vanishes-at-large-primes` already excludes
arbitrary-depth, arbitrary-weight primary sectors for p>=11. For those
primes the present argument is an independent proof of the same sector
conclusion, with a finite tracial coordinate formulation. Its new scope
within this repository is p=2,3,5,7, especially the arbitrary-weight
2-primary sector left outside
`lambda-exact-face-of-the-collapse-closes`.

Combining the all-prime primary theorem with the coprime congruence-slot
argument and Kazhdan--Jones uniform containment excludes the entire
genuine-congruence coordinate face of the scalar relative witness for
every prime. At p=2 this removes the scale-spread exact profiles without
a flatness assertion or any metaplectic transport dictionary. It does
not remove approximate lattice tuples without genuine coordinate lifts.
No nonhyperlinear existence conclusion follows until that remaining
sector is excluded by a separate argument.
