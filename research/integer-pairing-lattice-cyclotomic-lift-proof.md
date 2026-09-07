---
rg: 2
id: integer-pairing-lattice-cyclotomic-lift-proof
kind: route
title: Extend the pairing character through Smith coordinates and reduce a characteristic-zero inverse identity
target: cyclotomic-liftable-cancellation-pairs-have-no-inverse-defect
requires: []
artifacts:
  - research/artifacts/cancellation-phase-lift-literature-audit-2026-09-07.md
  - research/artifacts/c4-cancellation-needs-eighth-root-phases-2026-09-07.md
---

Use the notation of the claim. All groups are arbitrary and all sums
in group rings have finite support. We use the classical theorem that
C[G] is directly finite; one proof embeds it faithfully in the finite
group von Neumann algebra. The signature antecedent and references are
recorded in the attached literature audit.

## The exact lattice obstruction

Put L=im V subset Z^(m+n). Under (CPL1), the rule

    chi(Va)=(-1)^(sum_e a_e)

is a well-defined homomorphism L->{1,-1}. Indeed two presentations of
the same vector differ by an integral kernel vector, whose coordinate
sum is even. Conversely any character with chi(v_e)=-1 for every e
forces (CPL1). Changing the orientation of a pair replaces its vector
by its negative and its coefficient in any relation by its negative;
the parity of the total coefficient sum is unchanged.

Take Smith coordinates for the inclusion of L into the ambient free
abelian group. There is a basis b_1,...,b_(m+n) with

    L=direct_sum_(i=1,...,r) d_i Z b_i,
    d_i>0, d_i divides d_(i+1).

Let epsilon_i=chi(d_i b_i). If epsilon_i=1, set z(b_i)=1. If
epsilon_i=-1, write d_i=2^h o with o odd and choose a primitive
2^(h+1)-th root of unity for z(b_i). Then

    z(b_i)^(d_i)=(-1)^o=-1=epsilon_i.

Set z(b_i)=1 for i>r. These basis values define a character
z:Z^(m+n)->mu_(2^N) extending chi for some finite N>=1. Therefore

    z(e_i)z(f_j)=-z(e_k)z(f_l)

for every prescribed pair. This argument includes possible nonsaturation
of L; discarding that torsion would incorrectly reduce the test to signs.

## Lift the two factors, then reduce the reverse identity

Write alpha_i=z(e_i), beta_j=z(f_j), and
lambda=(alpha_(i_0) beta_(j_0))^(-1). In the group algebra over
O=Z[zeta_(2^N)] define

    B_tilde=sum_i alpha_i [t_i],
    A_tilde=lambda sum_j beta_j [s_j].

Every paired pair of cells contributes zero to B_tilde A_tilde;
the pivot contributes one. Even if distinct prescribed pairs share
their product label, their separate zero contributions remain zero.
Thus B_tilde A_tilde=1 in O[G]. Its injection into C[G] and direct
finiteness there imply A_tilde B_tilde=1. Faithfulness of the coefficient
embedding brings this equality back to O[G].

There is a surjective ring map

    O -> F_2,       zeta_(2^N) -> 1.

For N>=1 its kernel is (1-zeta_(2^N)); equivalently the cyclotomic
polynomial X^(2^(N-1))+1 evaluates to 2 at X=1. Every chosen phase,
and lambda, maps to one. Applying this coefficient map to the reverse
identity gives AB=1 in F_2[G]. No assertion that the support group is
residually finite, sofic, or amenable is used.

## A bounded, independently checkable alternative

Writing the phase values of the ambient basis as powers of one primitive
2^N-th root gives exactly (CPL3). Conversely, if (CPL3) holds and
Va=0, pairing q with Va gives

    0=2^(N-1) sum_e a_e mod 2^N,

so the coordinate sum is even. Thus (CPL1) and existence of (CPL3)
are equivalent, and negating them gives precisely (CPL2).

The Smith construction permits

    N=max(1, 1+max_(epsilon_i=-1) v_2(d_i))

with the inner maximum omitted if there are no negative directions.
In particular N<=1+v_2(d_r) when r>0. Each column v_e has norm two:
distinct equal-product cells cannot share a row or a column when the
support labels on each side are distinct. Every nonzero r by r minor
of V therefore has absolute determinant at most 2^r by Hadamard's
inequality. The product d_1...d_r is the greatest common divisor of
these minors, hence is at most 2^r. Consequently v_2(d_r)<=r. Finally
every column has separate row sum and column sum zero, so
r<=m+n-2. These observations give the claimed support-only bound.

For a reliable exact implementation, use the full integral kernel, not
an arbitrary rational nullspace basis with independently cleared
denominators. Such vectors can generate a proper sublattice and miss
odd relations. If P V Q is a Smith diagonalization with P,Q unimodular,
the last |E|-r columns of Q form an integral kernel basis. An odd
coordinate sum in one of these columns supplies (CPL2); if all sums
are even, every integral relation has even sum and the phase construction
applies. Both a displayed relation and a displayed phase-exponent vector
can be checked using finite integer arithmetic alone.

## Scope for construction

Over F_2 every strict pair would admit the stated cell pairing, so it
must pass the odd-integral-relation requirement for each pairing one
chooses to test. Finding one pairing with a phase lift rules the pair
out globally, independent of search radius. Conversely an odd integral
relation only prevents this particular characteristic-zero lift; it
does not detect AB-1 and is not a nonfiniteness certificate. It also
does not validate word inequalities in a universal presentation.
