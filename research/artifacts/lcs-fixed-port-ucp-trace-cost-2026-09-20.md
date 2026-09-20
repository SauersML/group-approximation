# Fixed-port completely positive decoding requires unbounded trace cost

20 September 2026. This is a quantitative extension of the common-corner
audit, not a solution of perfect-completeness hardness. It permits
nonreducing unital completely positive (UCP) maps but retains the specified
port observables. It does not constrain arbitrary replacement observables.

## 1. Exact setup and the input already proved

Use H, rho, its eight involutory generators, and

    R_m = rho tensor [1 direct-sum (rho tensor conjugate(rho))]^tensor m,
    d_m = 4 times 17^m,
    b = (1+X)(1-U_0)/4 in C[H]

from [the common-corner proof](lcs-auth-proper-corner-audit-2026-09-20.md).
Since X and U_0 commute and are involutions, b is a projection in C[H]
and B_m=R_m(b) is a matrix projection. It is zero in the original honest
four-dimensional model, not in every amplification.

That proof establishes the following finite facts, independently of any
channel. For each positive integer N, choose words g_1,...,g_N whose
conjugates of the three projective classes X,U_0,XU_0 are pairwise
disjoint. Put

    A = (1/N) sum_i g_i b g_i^-1,   D=A-1/4.

The canonical scalar-character trace satisfies tau_sc(D^2)=3/(16N).
The coefficient-l1 norm of D is at most 3/4. The exact character formula

    tr(R_m(h)) = chi(h) [(1+16|chi(h)|^2)/17]^m

therefore gives, for a constant beta_N<1 depending only on the finite
word support in D^2,

    tr(R_m(D)^2) <= 3/(16N)+(9/16) beta_N^m.          (1)

For example, take beta_N to be the maximum of
`(1+16|chi(h)|^2)/17` over nonscalar words in that support; the empty
maximum may be taken to be zero. Contributions from scalar words agree
exactly with tau_sc. The existence of the disjoint conjugates, the
ICC scalar quotient, and the character formula are proved in the cited
artifact. No new numerical search is needed here.

## 2. Statement: bounded trace cost cannot decode these fixed ports

Let Phi_m:M_(d_m)(C)->M_(k_m)(C) be UCP maps. All matrix traces below
are normalized. Define the state phi_m=tr_(k_m) composed with Phi_m.
Suppose C_m is a number such that

    phi_m(a) <= C_m tr_(d_m)(a) for every positive matrix a.   (2)

Such a finite C_m always exists at a fixed dimension. The condition of
interest is a bound uniform in m. Equivalently, the density of phi_m
relative to normalized input trace has operator norm at most C_m.

For the eight prescribed self-adjoint involutory ports s, define

    eta_m = max_s sqrt(tr_(k_m)(I-Phi_m(R_m(s))^2)).          (3)

The quantities under the square root are nonnegative, because UCP maps
send self-adjoint contractions to self-adjoint contractions. Let L_N be
the maximum word length of the chosen g_i in these eight ports. Then

    max(0,1-4 phi_m(B_m)-8 L_N eta_m)^2
        <= C_m (3/N+9 beta_N^m).                           (4)

In particular, if eta_m tends to zero and phi_m(B_m) tends to zero,
then C_m tends to infinity. This is divergence, not merely absence of
one globally bounded choice: any bounded subsequence contradicts (4)
after choosing N sufficiently large.

## 3. The finite-dimensional channel estimate

We give the calculation, rather than assume a stability theorem for
channels. A UCP map has a finite-dimensional dilation

    Phi(a)=V^* pi(a) V,   V^*V=I.

For completeness, this matrix fact follows by factoring its positive
Choi matrix `[Phi(E_ij)]` as a sum of rank-one positive matrices.
Reshaping those vectors supplies matrices W_l with
`Phi(a)=sum_l W_l^* a W_l`; unitality gives `sum_l W_l^*W_l=I`.
Stacking the W_l gives the asserted isometry V and pi(a)=a tensor I
up to the choice of tensor ordering. Positivity of the Choi matrix
follows by applying complete positivity to `[E_ij]`, itself positive.

Write E=VV^*. For a unitary u and a contraction x, the defect

    T=Phi(ux)-Phi(u)Phi(x)=V^* pi(u)(I-E)pi(x)V

satisfies

    TT^* <= V^*pi(u)(I-E)pi(u)^*V
           = I-Phi(u)Phi(u)^*.

Consequently its normalized Hilbert--Schmidt norm is at most the
square root of the trace on the right. Applying this to adjoints
also bounds `Phi(xu)-Phi(x)Phi(u)` by the square root of
`tr(I-Phi(u)^*Phi(u))`. For an involution u these are the same number
eta(u) used in (3).

If phi=tr composed with Phi, cyclicity of output trace now gives

    |phi(uxu)-phi(x)| <= 2 eta(u).                         (5)

Indeed, compare Phi(uxu) with Phi(u)Phi(xu) using the left defect,
and Phi(x)=Phi((xu)u) with Phi(xu)Phi(u) using the right defect.
The two middle traces agree, and normalized trace is bounded by
normalized Hilbert--Schmidt norm. Successive conjugation along a
port word g of length ell therefore gives

    |phi(R_m(g) B_m R_m(g)^*)-phi(B_m)| <= 2 ell eta_m.    (6)

Every intermediate conjugate of B_m is a contraction. This argument
does not assume phi is a trace or that the channel is multiplicative.
The exact zero-defect case is the familiar multiplicative-domain
phenomenon; the standard dilation and Schwarz tools are not claimed
as new results here.

## 4. Proof of the quantitative bound

Average (6) over the N conjugators. It yields

    phi_m(R_m(A)) <= phi_m(B_m)+2 L_N eta_m.

The state Cauchy--Schwarz inequality and (2) imply

    |phi_m(R_m(D))|^2 <= phi_m(R_m(D)^2)
                      <= C_m tr(R_m(D)^2).

On the other hand the preceding upper bound on phi_m(A), together
with D=A-1/4, implies

    max(0,1/4-phi_m(B_m)-2 L_N eta_m)
        <= |phi_m(R_m(D))|.

Insert (1) and multiply by sixteen to obtain (4). If C_m had a
subsequence bounded by C while both errors vanished, (4) would give
`1<=3C/N` for every fixed N. Choosing N>3C proves the assertion.

## 5. What this does and does not rule out

Suppose the eight fixed port images under Phi_m are actual unitaries.
Then eta_m=0. The defect estimates above show that Phi_m is
multiplicative whenever a port is one factor, and therefore on their
generated algebra. Write X'=Phi_m(R_m(X)) and U'=Phi_m(R_m(U_0)).
If a projection q on the output space gives the literal controlled form

    U'=(I-q)+X'q,

then `(I+X')(I-U')=0`, so Phi_m(B_m)=0. Bound (4) applies. Approximate
variants are precisely governed by (3) and phi_m(B_m), without silently
assuming that small word errors imply these two analytic conditions.

A normalized compression to a common reducing corner P is a special
case, with C=1/tr(P), zero port variance, and zero b expectation on a
good literal corner. Thus the earlier vanishing-corner result is
recovered. Here the channel need not be a reducing compression at all.

There are nevertheless exact channels of large trace cost: compress
onto the original honest summand, which has relative dimension 17^-m.
Its trace cost is 17^m. Accordingly we exclude uniformly bounded cost,
not the existence of every channel or any good small summand.

This says nothing about arbitrary new word ports, different anchors,
context-dependent channels without a common map, nonlinear matrix
readouts, or non-word replacement observables. Nor does bare
YES-instance completeness require extending this particular honest
model. No HALT-positive source or perfect-completeness reduction is
constructed or refuted. The use of a UCP map is in the Heisenberg
observable direction; it must not be confused with a trace-preserving
Schrodinger channel in the reverse direction.

## Provenance and verification boundary

The specific family, disjoint-conjugate construction, and finite trace
bound are prior Cairn work in the linked common-corner artifact. The
new deduction here is (4) and its fixed-port UCP trace-cost consequence.
The finite-dimensional dilation/Schwarz/multiplicative-domain principles
are standard operator algebra, with the needed calculations supplied
above. No priority is claimed for those general principles. This is
an informal mathematical proof, not a Lean certification or an external
human referee report.

Independent internal review checked the two eta conjugacy estimate,
Stinespring inequality, normalized traces, constants in (4), divergence
rather than unboundedness, and the fixed-port scope. No repairs were
required. The review does not certify the full open source problem.
