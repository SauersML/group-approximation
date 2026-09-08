# Exact arithmetic overlap forces the denominator-primary factor to vanish

Date: 2026-09-08. This proof concerns genuine finite congruence lattice
representations. It does not construct exact representatives for arbitrary
lattice microstates and does not prove existence of a nonhyperlinear group.

## Statement and exact hypotheses

Fix a prime p, and put

    C = SL_3(Z),       K = SL_3(Z_p),
    h = diag(p,1,p^-1),
    D = C intersect h^-1 C h,
    D_p = K intersect h^-1 K h.

Let (M_n,tau_n) be finite tracial von Neumann algebras with faithful
normalized traces. Suppose sigma_n:C -> U(M_n) is a genuine homomorphism
factoring through SL_3(Z/q_n), H_n is a unitary in M_n, and on a fixed
finite Kazhdan set S_D of the finite-index subgroup D,

    delta_n = max_(d in S_D)
      ||H_n sigma_n(d)-sigma_n(h d h^-1)H_n||_2 -> 0.          (1)

Write q_n=p^(a_n)m_n, with (p,m_n)=1. CRT gives commuting genuine
representations rho_n:K -> U(M_n) and
beta_n:SL_3(Z/m_n) -> U(M_n), such that

    sigma_n(c)=rho_n(c) beta_n(c mod m_n).

Here rho_n factors through SL_3(Z/p^(a_n)); when a_n=0 it is trivial.
Then

    sup_(k in K) ||rho_n(k)-1||_2 -> 0.                      (2)

Thus sigma_n^cop(c)=beta_n(c mod m_n) is a genuine coprime
representation and

    sup_(c in C) ||sigma_n(c)-sigma_n^cop(c)||_2 -> 0.         (3)

There is no bound on conductors, multiplicities, coprime factors, or
dimensions, and no regular-character assumption. Matrices with normalized
trace are a special case. The assertions also hold with limits along a
free ultrafilter: replace subsequential weak limits below by the unique
weak ultralimits in the indicated compact space.

## 1. A fixed overlap gives an exact large intertwiner

Let kappa_D>0 be a Kazhdan constant for S_D. On L^2(M_n,tau_n) use

    U_n(d)T = sigma_n(h d h^-1) T sigma_n(d)^*.

This is an exact representation. Project H_n onto its invariant
subspace to get T_n. Property T gives

    ||T_n-H_n||_2 <= eta_n := delta_n/kappa_D,
    T_n sigma_n(d)=sigma_n(h d h^-1)T_n  for all d in D.      (4)

The image of D in the product of these two finite congruence images is
finite. This projection is a finite average; in particular T_n belongs
to M_n. Write e_n=supp(T_n^*T_n), f_n=supp(T_n T_n^*).
The polar partial isometry intertwines the representations on these
corners, and

    tau_n(e_n)=tau_n(f_n) >= 1-eta_n^2.                     (5)

Indeed T_n(1-e_n)=0 and
||(T_n-H_n)(1-e_n)||_2^2=tau_n(1-e_n). Also

    sup_(d in D)
      ||H_n sigma_n(d)-sigma_n(h d h^-1)H_n||_2 <= 2 eta_n.  (6)

These equations hold uniformly for every d in D. There is no estimate
for long words in approximate generators.

## 2. Joint CRT removes the coprime factor

Fix n and k in D_p. Surjectivity of integral reduction for SL_3 and
CRT give d in C with

    d = k mod p^(a_n+2),       d = I mod m_n.               (7)

These are compatible prescribed determinant-one residues modulo
p^(a_n+2)m_n. Integral reduction is onto because elementary matrices
generate SL_3 over these finite quotient rings.

Conjugation by h changes entry valuations by at most two. The
conditions defining D_p are divisibility conditions modulo p^2.
Thus d belongs to D, and

    h d h^-1 = h k h^-1 mod p^(a_n),
    h d h^-1 = I mod m_n.                                  (8)

The second congruence uses that p is invertible modulo m_n. Both
coprime factors in (4) are identities. For every k in D_p,

    T_n rho_n(k)=rho_n(h k h^-1)T_n,                        (9)
    ||H_n rho_n(k)-rho_n(h k h^-1)H_n||_2 <= 2 eta_n.        (10)

The integral lift may depend on n and k; (4) was already uniform.
The precision a_n+2 is necessary to allow for division of entries by
p^2. This handles mixed levels and correlated isotypic multiplicities
without separating irreducible blocks.

## 3. Exact positive Fourier measures

Put K_j=ker(K -> SL_3(Z/p^j)) and l_j=p^j sl_3(Z_p).
For odd p these groups are uniform for j>=1; matrix exponential
identifies their Lazard Lie algebras with l_j. At p=2 use j>=2.

First suppose p is odd and fix r>=1. Boyarchenko--Sabitova Theorem 2.6
gives the exact orbit character formula on K_r. Normalizing each
irreducible character at the identity gives a uniform probability
measure on its finite coadjoint orbit in the additive dual l_r^vee.
Consequently there is a finitely supported probability measure mu_n
on l_r^vee such that

    tau_n(rho_n(exp X)) = integral lambda(X) d mu_n(lambda)
       for every X in l_r.                                (11)

For general finite tracial coordinates, decompose the finite group
image algebra into matrix blocks: its trace is a positive weighted
sum of normalized irreducible characters. The weights may be real.
Character conjugation invariance and uniqueness of additive Fourier
transform show that mu_n is invariant under the full compact group K.

Use the dual pullback convention

    R_g(v)(X)=v(Ad(g)X),

so that the Fourier transform of (R_h)_*mu evaluates the character at
h exp(X)h^-1. The family R_g is the inverse of another common
coadjoint convention; the groups of transformations and their
invariant measures are identical.

Choose fixed s>=r+2. Then Q=K_s is contained in D_p and hQh^-1 is
contained in K_r. Equation (9) and polar decomposition give common
corner representations of Q, of trace t_n>=1-eta_n^2. The two
trace characters, for rho_n|Q and rho_n composed with Ad(h)|Q,
each decompose into the same positive character of mass t_n and a
positive remainder of mass 1-t_n. The equality of the common
characters follows by traciality and the polar intertwiner.

Apply the positive orbit formula to these corners as representations
of Q. The resulting Fourier probability measures on l_s^vee differ
in variation norm by at most

    2(1-t_n) <= 2 eta_n^2.                                 (12)

By uniqueness, these are the restrictions of mu_n and (R_h)_*mu_n to
l_s. This total-variation conclusion uses an actual common
representation. Mere uniform closeness of character values on
growing quotients would not imply it.

Only two fixed uniform principal subgroups need the orbit formula.
No formula on the nonuniform parahoric D_p is used. Exponential
conjugation and additive Fourier restriction are exact; there is no
conductor-dependent BCH error.

## 4. Fattening and projective compactification

Fix a nontrivial continuous additive character of Q_p and let
V=sl_3(Q_p)^*. The additive dual l_j^vee identifies with V/L_j,
where L_j is the compact open annihilator of l_j. Use the abstract
dual vector space: no integral perfect trace pairing is required
at p=3.

Replace each atom of mu_n by normalized additive Haar measure on its
coset of L_r, obtaining a probability measure nu_n on V. It is exactly
K-invariant since L_r is K-invariant. Write a_s for normalized Haar
measure on L_s. The inclusion Ad(h)l_s subset l_r gives

    L_r subset L_s,       R_h L_r subset L_s.

Restriction to l_s is quotienting by L_s. Equation (12) is therefore

    ||nu_n*a_s - ((R_h)_*nu_n)*a_s||_var <= 2 eta_n^2.       (13)

This does not require R_h to preserve L_r.

Embed V in X=P(V direct-sum Q_p) by v -> [v:1], with boundary
Y=P(V direct-sum 0)=P(V). The space X is compact metrizable.
Translations by elements of the fixed compact lattice L_s extend
continuously to X, preserve V, and fix every boundary point.
Averaging these translations is weakly continuous on probability
measures on X. The linear maps R_g also extend to X, acting
trivially on its last coordinate.

For any subsequential weak limit nu on X, equation (13) gives
nu*a_s=((R_h)_*nu)*a_s. Restriction to the boundary then gives

    nu|Y = (R_h)_*(nu|Y).                                  (14)

This boundary measure is also K-invariant. Positive boundary mass
would give a probability measure on P(V) invariant under K and R_h.

Such a measure does not exist. The eigenspaces W_j of R_h, for
weights j=-2,-1,0,1,2, have distinct eigenvalue absolute values and
are all proper. A projective vector with nonzero components in more
than one weight space is not recurrent under forward powers of R_h:
it converges to its component with largest absolute eigenvalue.
Poincare recurrence forces an invariant measure to be supported on

    Sigma = union_j P(W_j).

Its closed support is K-invariant. For any support point [v], its
K-orbit lies in Sigma. The compact group SL_3(Z_p) is Zariski dense
in the connected algebraic group SL_3 over Q_p. Hence the whole
algebraic orbit of [v] lies in Sigma. That orbit is irreducible,
so it lies in one P(W_j). But its linear span is V: the coadjoint
representation is irreducible over the characteristic-zero field
Q_p. This contradicts the properness of W_j.

Thus every subsequential weak limit has zero mass on Y. The measures
nu_n are therefore tight on V. Indeed, failure of tightness gives a
subsequence with a fixed positive mass outside an increasing
exhaustion by compact balls; a further weak limit on X then has that
positive mass on Y.

Angular information is retained throughout. A Følner distribution of
conductor depths alone need not admit K-invariant Fourier measures
with the joint covariance (13).

## 5. Tightness and root contraction kill the primary factor

Given epsilon>0, tightness gives a compact F in V carrying at least
1-epsilon of nu_n for all sufficiently large n. For some sufficiently
large j>=r, every v in F is trivial on l_j under the additive
character. Equation (11) implies, uniformly for k in K_j,

    ||rho_n(k)-1||_2^2
       =2(1-Re tau_n(rho_n(k))) <= 4 epsilon.

Consequently

    lim_(j->infinity) limsup_(n->infinity)
      sup_(k in K_j)||rho_n(k)-1||_2 = 0.                   (15)

Let x(t)=I+tE_12. It belongs to D_p for all t in Z_p, and
h x(t)h^-1=x(pt). For each fixed integer j, iterate (10):

    ||H_n^j rho_n(x(1)) H_n^-j-rho_n(x(p^j))||_2
       <= 2j eta_n.

Since x(p^j) belongs to K_j, first taking limsup_n and then j to
infinity in (15) gives ||rho_n(x(1))-1||_2 -> 0.
Conjugation by fixed signed permutation matrices of determinant one
in K gives the same conclusion for every elementary generator
I+/-E_ij of C.

Apply property T of C to left multiplication by the genuine
representation rho_n|C on L^2(M_n,tau_n), with vector 1.
Let P_n be the projection onto the trivial part of the finite image
of rho_n: it is the finite group average of rho_n. Density of C in
K identifies C- and K-invariants. The projection of 1 onto invariant
vectors is P_n, so, for a fixed elementary Kazhdan generating set S_C,

    1-tau_n(P_n)
      <= kappa_C^-2 max_(c in S_C)||rho_n(c)-1||_2^2 -> 0.

Every rho_n(k)-1 is supported on 1-P_n; therefore

    sup_(k in K)||rho_n(k)-1||_2
       <= 2 sqrt(1-tau_n(P_n)) -> 0.

This proves (2), and multiplication by the commuting coprime factor
proves (3).

## 6. Extension to the prime two

Fix r>=2 and apply Boyarchenko--Sabitova Theorem 2.8 to P=K_r.
Part (b) states that each irreducible character restricted to
P^2=K_(r+1) is a multiple of the inverse Fourier transform of an
orbit indicator on l_(r+1)^vee. Evaluation at the identity shows
that the normalized character is the Fourier transform of the
uniform probability on that orbit.

Construct mu_n on l_(r+1)^vee using this restriction. It is positive
and exactly K-invariant by Fourier uniqueness. Choose s>=r+2.
The common Q=K_s corner representations from (9), and their two
remainders, have positive Fourier measures upon restriction to
Q^2=K_(s+1), again by Theorem 2.8. Their measures on l_(s+1)^vee
differ by at most 2 eta_n^2 in variation norm.

Since Ad(h)l_(s+1) subset l_(r+1), uniqueness identifies them with
the restrictions of mu_n and (R_h)_*mu_n. In Sections 4--5 replace
the frequency index r by r+1 and comparison index s by s+1.
Every remaining step is unchanged. No bijection between individual
irreducibles and orbits at p=2 is asserted or needed.

## Consequence and the unresolved headline gap

In a relative witness for SL_3(Z) subset SL_3(Z[1/p]), suppose
the lattice has genuine finite congruence coordinate representatives.
Its h-coordinate and those exact representatives satisfy (1), by
the ultraproduct group relations on the fixed finite set S_D.
Equation (3) replaces the lattice representatives by coprime genuine
ones without changing the ultraproduct images or their containment
in coordinate carrier algebras.

The established coprime congruence-slot argument and uniform
Kazhdan--Jones containment then exclude such a witness. This removes
all denominator-primary sectors in that exact-coordinate class,
including arbitrary conductor mixtures and mixed levels. General
finite tracial coordinates are permitted provided the prescribed
lattice representatives are genuine finite congruence images.

Arbitrary scalar relative witnesses still allow approximate lattice
tuples without exact congruence lifts. For those tuples (4) is not an
exact group action, CRT does not supply rho_n, and (11) has no
justified positive character decomposition. Neither this argument
nor Jones containment supplies the missing correction theorem.
Nonhyperlinearity of the arithmetic double and general existence of
a nonhyperlinear group remain unproved here.

## Sources and audit boundaries

The external input is [Boyarchenko--Sabitova,
arXiv:math/0608126](https://arxiv.org/pdf/math/0608126), Theorem 2.6
for odd primes and Theorem 2.8 for the square restriction at two.
The compactification, joint CRT reduction, and primary-vanishing
argument are the present deduction, not claims attributed to that
paper. No conductor-dependent approximation to its formulas is used.

For the final coprime consequence see the existing route
sl3-re-coprime-face-closes-by-jones-kazhdan and its artifact
research/artifacts/kazhdan-jones-uniform-carrier-containment-2026-09-08.md.
This does not restore the invalid assertion that a varying congruence
slot belongs to the algebra generated by constant lattice sequences.
The coordinate containment theorem handles that varying slot.

