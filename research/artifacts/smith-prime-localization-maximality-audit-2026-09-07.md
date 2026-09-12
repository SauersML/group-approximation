# Exact arithmetic maximality and finite-word transfer

Independent mathematical audit, 2026-09-07. This is a handwritten proof,
not a proof-assistant certificate. It establishes an arithmetic input to
the relative-embeddability lane; it does not establish a nonhyperlinear
group or produce a commutant leak.

## Scope and literature

For every prime p and n>=2, the inclusion

    SL_n(Z) < SL_n(Z[1/p])

is algebraically maximal. Repository searches for arithmetic maximality,
overgroups of the integral group, and Smith-based maximality found no
existing statement of this fact before these files were added.

The fact is already in the primary literature:

* Tsachik Gelander and Chen Meiri, *Maximal subgroups of SL(n,Z)*,
  Transformation Groups 21 (2016), 1063--1078,
  [arXiv:1511.05767](https://arxiv.org/pdf/1511.05767).
  The inspected 18-page PDF states the maximality fact on printed page
  16, in Section 7 immediately after Question 7.1, and also uses it at
  the end of Section 6. The discussion attributes the observation to
  Yair Glasner. This is direct algebraic maximality, not merely a
  statement about a maximal compact p-adic subgroup.
* Yves Cornulier, *Finitely presented wreath products*,
  [author PDF](https://www.normalesup.org/~cornulier/wrea_fp.pdf),
  Remark 3.3 on printed page 8, explicitly records that SL_2(Z) is a
  maximal subgroup of infinite index in SL_2(Z[1/p]) for every prime p.
* Richard Stanley, *Smith Normal Form in Combinatorics*,
  [arXiv:1602.00166](https://arxiv.org/pdf/1602.00166),
  Theorem 2.1(4), records existence of Smith normal form over principal
  ideal rings, including the integers. The route only needs the
  classical integer case.

No novelty claim is made for maximality or Smith normal form. The
explicit word count below makes the particular commutator application
reviewable without a topological inference.

## Full arithmetic argument

Let C=SL_n(Z), A=SL_n(Z[1/p]), and g in A minus C. Put K=<C,g>.
Choose k>=0 with M=p^k g integral. Smith normal form supplies U,V in
GL_n(Z) and positive integers d_1,...,d_n satisfying

    U M V=diag(d_1,...,d_n),
    product_i d_i=p^(kn).

Every d_i is a power p^(beta_i), since their positive product is a
power of the single prime p. Dividing by p^k gives

    U g V=D=diag(p^(a_1),...,p^(a_n)),
    a_i=beta_i-k,   sum_i a_i=0.

The determinant of D is positive, so det(U)det(V)=1. Both determinants
are +1 or both are -1. In the latter case J=diag(-1,1,...,1) gives
U'=J U and V'=V J with determinants +1 and U'gV'=JDJ=D. Thus all
changes of basis may be taken in C, and D belongs to K.

The exponent vector is nonzero: if D=I, then g=U^(-1)V^(-1) is integral.
Choose i,j with a_i<a_j, and put m=a_j-a_i>0. Direct conjugation gives

    D(I+E_ij)D^(-1)=I+p^(-m)E_ij.

Because E_ij^2=0,

    (I+p^(-m)E_ij)^(p^(m-1))=I+p^(-1)E_ij.

Thus K contains one fractional transvection. Determinant-one signed
permutation conjugations move it to any ordered pair of different
indices, with a possible coefficient sign that inversion corrects.
For n=2 the determinant-one matrix [0 1; -1 0] performs the needed
swap, so this step does not require a third index.

Set e_rs(t)=I+tE_rs. All integral e_rs(t) lie in C. In the r,s block,

    e_rs(p)e_sr(-1/p)e_rs(p) = [ 0      p ],
                              [ -1/p   0 ]

and multiplying this by

    (e_rs(1)e_sr(-1)e_rs(1))^(-1)

gives diag(p,p^(-1)) in that block. Hence K contains all elementary
diagonal p-power pairs h_rs(p), and their integer powers. If sum_i b_i=0,

    product_(r<n) h_rn(p)^(b_r)=diag(p^(b_1),...,p^(b_n)).

For any h in A, repeat the same integer Smith reduction to obtain
U_h h V_h equal to a diagonal of this form, with U_h,V_h in C. The
diagonal is already in K, so h belongs to K. Therefore K=A. Since
e_12(1/p) belongs to A minus C, this proves maximal proper inclusion.

This proof uses only a single-prime denominator condition. For a
localization at two different primes p,q, the analogous integral
subgroup is not maximal: SL_n(Z[1/p]) is an intermediate proper
subgroup of SL_n(Z[1/p,1/q]). No multiprime maximality is asserted.

## Explicit count and transfer to any tracial representation

Keep the Smith exponent difference m for g. In a word over
C union {g,g^(-1)}, the diagonal D=U g V has one g letter. Therefore
D e_ij(1)D^(-1) has two letters from {g,g^(-1)}. Raising it to the
positive integer p^(m-1) gives at most

    L_0=2 p^(m-1)

such letters in e_ij(1/p). Conjugating by C and taking inverses preserve
the count, so every fractional root e_rs(plus or minus 1/p) has this
bound. The word above for h_rs(p) uses exactly one fractional-root
factor and otherwise only C factors, hence also has the bound L_0.

Let U_h h V_h=diag(p^(b_1),...,p^(b_n)) be a determinant-one Smith
reduction of a fixed h outside C. The product of h_rn(p)^(b_r) therefore
produces a word for h with at most

    L_(g,h)=2 p^(m-1) sum_(r<n)|b_r|

g letters, counting both signs. This is a positive integer, since a
nonzero exponent vector of sum zero cannot have its first n-1 entries
all zero. Cancellation may shorten the word; the displayed expression
is a sufficient upper bound.

Suppose M is a finite tracial von Neumann algebra, pi:A->U(M) is an
exact representation, and e in M commutes with pi(C). Write the above
word for h and use

    [e,uv]=[e,u]v+u[e,v].

The 2-norm is unchanged by left or right multiplication by a unitary,
and ||[e,u^(-1)]||_2=||[e,u]||_2. Every C letter contributes zero, so

    ||[e,pi(h)]||_2 <= L_(g,h)||[e,pi(g)]||_2.

Thus one nonzero h commutator makes every outside g commutator nonzero.
Equivalently, the commutation stabilizer of e is exactly C whenever it
contains C and is a proper subgroup of A. This conclusion uses an exact
representation and exact commutation with C, as available in a tracial
ultraproduct. It is not an estimate for arbitrary approximate maps
without additional word-defect terms.

For a projection e, the expectation onto B={e}' cap M removes the two
off-diagonal corners. Their orthogonality gives, for a unitary u,

    ||E_B(u)||_2^2=1-||[e,u]||_2^2.

If delta=||[e,pi(h)]||_2>0, this proves

    ||E_B(pi(g))||_2^2 <= 1-delta^2/L_(g,h)^2 <1.

The bound is dimension independent for fixed matrices g,h, but need
not be uniform in g. Tensor powers can therefore damp each outside
element separately. The argument supplies neither the projection e
nor a decision on existence of a leak in a Connes-embeddable model.
