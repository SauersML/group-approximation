# Finite additive order removes the full-defect hypothesis

Date: 2026-09-08. Mathematical proof, not a Lean verification claim.

Let R be a countable unital associative ring. Suppose ts=1, put
Q=1-st, and suppose qQ=0 for an integer q>=2. We prove that every
homomorphism E_n(R)->U(Q_d), n>=4, kills every root e_ij(Q).

The universal ring

    R_q=Z<S,T | TS=1, q(1-ST)=0>

is finitely generated and countable. Write E=E_4(R_q), H=E_3(R_q)
in coordinates 1,2,3, and a=e_13(1-ST). The shift representation
over Z/q shows that 1-ST is nonzero of exact additive order q.
The composite-modulus artifact proves:

1. the defect ideal is M_fin(Z/q);
2. its finitary elementary group A=E_fin(Z/q) embeds normally in E;
3. for a standard exhaustion A_j containing a, every complex unitary
   representation sigma satisfies
   dim((Fix sigma(A_j))^perp)<=4 rank(sigma(a)-I).

Property (T) for H follows from Ershov and Jaikin-Zapirain,
*Property (T) for noncommutative universal lattices*,
Inventiones Mathematicae 179 (2010), 303--347, whose theorem covers
E_n(B) for every finitely generated associative unital ring B and
n>=3. See the [authors' accepted paper](https://m-ershov.github.io/Research/EL_n_accepted.pdf)
and [arXiv record](https://arxiv.org/abs/0809.4095).
This is a literature input for the integral universal ring, not a
claim that the repository's finite-field Lean theorem has that scope.

Here is the compression cell in full. Put e=1-ST and, for i=1,2,3,

    u_i=e_4i(T-1)e_i4(1)e_4i(S-1)e_i4(-T),
    u=u_3 u_2 u_1,
    c=[e_41(e),e_14(T)].

Using e^2=e, eS=Te=0, direct multiplication gives

    u = [[S,0,0,e],
         [0,S,0,eT],
         [0,0,S,eT^2],
         [0,0,0,T^3]],
    c=diag(1,1,1,1+eT).

All are elementary-group elements by their displayed words. For
i!=j in {1,2,3} and b in R_q,

    u e_ij(b)=e_ij(SbT)u.

Hence uHu^-1<=H. The displayed c commutes with H. Finally

    u c=e_12(e)u,
    [u c u^-1,e_23(1)]=e_13(e)=a.

These are the manuscript's rank-four compression-cell identities;
none uses fullness of e. They put a in D_E(H). Applying the
rank-weighted locally finite compression theorem with C=4 proves

    a in Rad_MF(E_4(R_q)).

The coefficient homomorphism R_q->R, S->s,T->t, induces the required
elementary-group homomorphism. Composing any norm-corona map of
E_4(R) with it kills e_13(Q). Stabilization into rank n and
conjugation by elementary signed permutation matrices gives every
off-diagonal position. Inverting a root changes a minus sign if
needed. These operations preserve MF invisibility.

If Q!=0, e_13(Q)!=I, so E_n(R) cannot be MF. If R has positive
characteristic and E_4(R) is MF, any pair ts=1 has Q of finite
additive order; the theorem forces Q=0. Thus st=1 and R is directly
finite.

For the binary Jacobson ring in rank five, the existing exact symbol
sequence and simple-kernel dichotomy identify the entire radical as
the finitary kernel, not just a nonzero subgroup of it.

## Limits

The argument uses property (T). The separate proof-provenance goal
excluding property (T) stays open. Arbitrary locally finite normal
subgroups need not satisfy the uniform support bound; that general
upgrade is not proved here. An idempotent of infinite additive order
is also outside this theorem. The new weighted-Hilbert theorem and
the composite-modulus assembly have not been formalized in Lean.
