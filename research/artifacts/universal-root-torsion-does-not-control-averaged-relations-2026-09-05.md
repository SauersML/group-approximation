# Universal root torsion does not control averaged root relations

Date: 2026-09-05. Analytic construction; no computation or prime enumeration.

This artifact gives canonical approximate representations of the full group
SL_5(Z) with exact universal root torsion and curvature already concentrated
on a reducing projection of quadratic rank. Nevertheless, the natural
power-defined root maps over the universal finite ring have a mean squared
Steinberg defect tending to 2. A second version satisfies even the individual
root spectral order and eigenspace divisibility restrictions coming from
three Heisenberg pairs.

These are obstructions to deriving an averaged finite-ring relation ledger
from those data without first making a coherent correction. The tuples are
explicitly close to exact representations. They do not obstruct flexible
stability, the MSC spectral count conclusion at a suitable cutoff, or a
construction that changes phases jointly.

## 1. Presentation, normalization, and the regular block

Write x_ij=I+E_ij, for distinct i,j in {1,...,5}, and use
[a,b]=a^{-1}b^{-1}ab. Fix the following finite presentation:

* [x_ij,x_kl]=1 when i != l and j != k;
* [x_ij,x_jk]=x_ik for pairwise distinct i,j,k;
* (x_12 x_21^{-1} x_12)^4=1.

This standard transvection presentation is recorded explicitly in
[Biswas, *Uniform two-generator presentations for SL_n(Z) with polynomial
complexity bounds*, Eq. (1)](https://arxiv.org/html/2604.17777v1#S1.E1).
In particular it contains r_0=[x_12,x_23]x_13^{-1}. Only this presentation
fact is imported; all matrix and averaging estimates below are direct.

For a d by d matrix, ||A||_{2,d}^2=Tr(A* A)/d. The defining defect delta is
the maximum ||U(r)-I||_{2,d} over this fixed finite presentation, with inverse
letters evaluated as adjoints.

Let p run through odd primes tending to infinity, let Q_p=SL_5(F_p), put
N=|Q_p|, and let rho_p be its left regular representation, pulled back to
SL_5(Z). The upper unitriangular subgroup has order p^10, so p^10 divides N.
The determinant-one diagonal sign subgroup has order 16, so 16 divides N.
Consequently N/p is divisible by p^9 and by 16.

Every x_ij has order p in Q_p. Its action on Q_p consists of p-cycles, hence
rho_p(x_ij) has each p-th root of unity as an eigenvalue with multiplicity
N/p. If g is a fixed nonidentity matrix in SL_5(Z), its reduction is
nonidentity for all sufficiently large primes: one nonzero entry of g-I
has only finitely many prime divisors. Therefore

    Tr(rho_p(g))/N = 0 eventually, for every fixed g != 1.          (UR1)

This is the canonical regular approximation property.

For either dimension d used below, set

    n = floor((2d)^(1/3)),     q = lcm(1,2,...,n).                (UR2)

This is the universal dimension-2d modulus established in
[the universal Schreier host artifact](universal-dimension-schreier-host-2026-09-05.md).
Here p <= n since d >= N >= p^10, and q is even. Thus p divides q.
Moreover, for n >= 3,

    q >= lcm(n,n-1,n-2) >= n(n-1)(n-2)/2.

The last inequality follows from the consecutive gcd identities and
gcd(n,n-2) <= 2. Since n^3/(2d) tends to 1, this proves q >= c d for an
absolute positive c eventually. In particular,

    1/q = o(1/sqrt(d)).                                         (UR3)

No prime distribution estimate is needed.

## 2. One family of phase-twisted tuples

Take a positive integer m, put d=N+m, and choose a phase lambda with
lambda^q=1 and lambda tending to 1. Define

    U_ij = rho_p(x_ij) direct_sum I_m,       (i,j) != (1,3),
    U_13 = lambda rho_p(x_13) direct_sum (-I_m).                  (UR4)

Every root generator satisfies U_ij^q=I exactly, because p divides q,
lambda^q=1, and q is even. Let P be the projection onto the last m
coordinates. It reduces every generator.

For a fixed word w, let e(w) be its exponent sum in x_13. Scalars commute
with all regular matrices, so the exact word formula is

    U(w) = lambda^{e(w)} rho_p(w) direct_sum (-1)^{e(w)} I_m.     (UR5)

For a true group relator, rho_p(w)=I_N. Every commuting relator has exponent
sum zero; the chosen Weyl relator has exponent sum zero; a root relator
[x_ij,x_jk]x_ik^{-1} has exponent sum -1 exactly when (i,k)=(1,3), and zero
otherwise. Thus

    delta^2 = (N/d)|lambda-1|^2 + 4m/d.                         (UR6)

There is no unspecified presentation constant in this identity. The r_0
defect attains it. More generally, (UR5) shows that every fixed true SL_5
relation, including every fixed Weyl identity, has defect tending to zero
whenever m/d tends to zero and lambda tends to 1. The example is not only
an approximate representation of a Heisenberg subgroup.

If additionally |lambda-1|=o(delta), the defining curvature off P has
operator norm o(delta), and

    tr_d(P) <= delta^2/4.

All nonzero hard singular values on P equal 2. For any fixed t in (0,2),
and any defining relator defect E=U(r)-I,

    || (E/delta) 1_{|E| <= t} ||_{2,d} -> 0.                    (UR7)

Indeed P contributes zero to this cutoff and the complementary norm is
bounded by |lambda-1|/delta. Thus the tuples already have the quadratic
rank, hard-curvature normal form used by QRC. Here the support is even
exactly invariant; lack of an invariant support is not the reason for the
averaging failure below.

Under the same assumptions, (UR1) and (UR5) imply canonicality: normalized
word traces tend to 0 for fixed nonidentity group elements and to 1 for
fixed identity words. The bad block has vanishing normalized dimension.

## 3. The power-defined averaged root ledger

Define maps on Z/qZ by

    X_ij(a)=U_ij^a.

They are well-defined and satisfy each individual root group's additive
law exactly. Since p divides q, the regular blocks also satisfy the
parameterized root commutator identity modulo p. Consequently, for a,b
in Z/qZ,

    [X_12(a),X_23(b)] X_13(ab)^*
       = lambda^{-ab} I_N direct_sum (-1)^{ab} I_m.             (UR8)

If lambda has exact order s dividing q, uniform residues modulo q induce
uniform residues modulo s, and character orthogonality gives

    (1/q^2) sum_{a,b mod q} lambda^{ab} = 1/s.                  (UR9)

For completeness, at a fixed a the average over b is 1 if s divides a
and 0 otherwise, and exactly 1/s of all residues a have that property.
Since q is even, the average of (-1)^{ab} is 1/2: both residues are odd
with probability 1/4. Therefore the exact mean squared defect is

    (1/q^2) sum_{a,b mod q}
      ||[X_12(a),X_23(b)] X_13(ab)^* - I||_{2,d}^2
       = (N/d)(2-2/s) + m/d.                                 (UR10)

In particular, the ledger error is macroscopic if s tends to infinity
and m/d tends to zero. The loss occurs even though all finite-presentation
relations and root-additivity relations are already controlled.

## 4. Rank-one hard curvature with the universal torsion order

Choose m=1, d=N+1, and lambda=exp(2 pi i/q), of order s=q. Equations
(UR3) and (UR6) give

    delta^2 = 4/d + O(q^{-2}),
    delta ~ 2/sqrt(d),
    |lambda-1| = O(1/q) = o(delta).                            (UR11)

Thus (UR7) applies with a rank-one reducing support. All U_ij are already
q-torsion. Yet the mean squared defect in (UR10) is exactly

    (N/d)(2-2/q) + 1/d -> 2.                                  (UR12)

In this example the arithmetic average in (UR9) is exactly 1/q, not merely
small along a favorable sequence.

Nearest-q-th-root spectral rounding fixes each generator, since its
spectrum already consists of q-th roots. Such independent torsion
rounding therefore cannot repair (UR12).

## 5. Stronger version: all spectral orders satisfy the dimension bound

The first version can have individual eigenvalue orders much larger than
floor((2d)^(1/3)), although they divide the universal modulus. To remove
this possible escape, choose instead

    m=N/p,    d=N(1+1/p),    lambda=exp(2 pi i/p).               (UR13)

Then s=p divides q, and (UR6) becomes

    delta^2 = 4/(p+1) + O(p^{-2}),
    delta ~ 2/sqrt(p),
    |lambda-1| = O(1/p) = o(delta).                            (UR14)

The reducing support has trace 1/(p+1), asymptotic to delta^2/4, so (UR7)
again holds. The sequence is again canonical.

Every eigenvalue of every U_ij now has order 1, 2, or p, all at most n
from (UR2). Multiplication by lambda merely permutes the p-th roots in
the good spectrum of U_13, preserving every multiplicity N/p. Since p is
odd, -1 is not in that good spectrum and has multiplicity m=N/p.

There is also no violation of the individual eigenspace divisibility
test obtained from three exact independent Heisenberg pairs. For a
primitive p-th root, the eigenspace dimension N/p is divisible by p^3,
since p^10 divides N. For the eigenvalue -1, its eigenspace dimension m
is divisible by 2^3, since 16 divides N/p. Eigenvalue 1 has no additional
divisibility requirement. These statements hold root by root; they do
not assert that joint Heisenberg relations are exact on those eigenspaces.

Thus independent spectral rounding to the set of roots of order at most
n, as well as rounding to q-th roots, leaves the tuple unchanged. The
individual spectral constraints of the universal conductor argument are
already satisfied. Nevertheless, (UR10) gives the exact value

    (p/(p+1))(2-2/p) + 1/(p+1)
       = (2p-1)/(p+1) -> 2.                                  (UR15)

This rules out repairing the implication merely by retaining the sharper
individual root-order bound or its eigenspace divisibility consequence.

## 6. What correction actually repairs the examples

For either version, replace U_13 by rho_p(x_13) direct_sum I_m and leave
the other generators unchanged. This produces the exact representation
rho_p direct_sum 1^m. The squared normalized cost is exactly (UR6), hence
the correction tends to zero.

More pointedly, remove only lambda from the good block. This modification
has normalized HS cost at most |lambda-1|=o(delta). The good-block part
of the averaged defect then vanishes exactly; its only remaining mean
squared error is m/d, which tends to zero. Therefore the averaged ledger
can change from nearly 2 to nearly 0 under a correction smaller than the
original defining defect scale.

The precise failed implication is:

    fixed SL_5 relators -> 0
    + canonicality
    + exact universal root torsion
    + QRC hard curvature on an invariant quadratic-rank support
    + even the individual bounded-order spectral restrictions
       does NOT force the power-defined averaged root ledger -> 0.

A construction of a useful finite-quotient ledger must coordinate root
phases or choose parameterized root maps by another jointly controlled
procedure. This artifact supplies no obstruction to such a procedure,
and no counterexample to existence of the desired low-energy spectral
mass after an appropriate correction or at an appropriate cutoff.
