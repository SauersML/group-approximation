---
rg: 2
id: smith-diagonal-extraction-proves-arithmetic-maximality
kind: route
title: Extract one fractional transvection by Smith normal form, then generate every prime-power diagonal
target: smith-prime-localization-maximality-and-word-transfer
requires: []
artifacts:
  - research/artifacts/smith-prime-localization-maximality-audit-2026-09-07.md
---

Write e_ij(r)=I+r E_ij. Fix g in A minus C and put K=<C,g>.
Choose k>=0 so that p^k g has integer entries. Integer Smith normal form
gives U,V in GL_n(Z) and positive diagonal entries whose product is
det(p^k g)=p^(kn). Each diagonal entry is therefore a power of p, and

    U g V = D=diag(p^(a_1),...,p^(a_n)),   sum_i a_i=0.

The positive determinant of D implies det(U)=det(V). If both are -1,
replace U by J U and V by V J, where J=diag(-1,1,...,1). Since J D J=D,
this makes U,V lie in C and preserves D. Hence D lies in K. Not all a_i
vanish, since otherwise g=U^(-1)V^(-1) would belong to C.

Choose a_i<a_j and let m=a_j-a_i>=1. Then

    D e_ij(1) D^(-1)=e_ij(p^(-m)),
    e_ij(p^(-m))^(p^(m-1))=e_ij(1/p).

Conjugating by determinant-one signed permutation matrices in C, and
inverting when needed to correct the sign, gives e_rs(1/p) in K for
every r!=s. This works also for n=2.

For each r!=s define

    w_rs(p)=e_rs(p)e_sr(-1/p)e_rs(p),
    h_rs(p)=w_rs(p)w_rs(1)^(-1).

On coordinates r,s the first matrix is [0 p; -1/p 0], and the second
is diag(p,p^(-1)); outside these coordinates both are the identity.
All displayed factors lie in K, since the integral factors lie in C.
Thus K contains every determinant-one diagonal p-power matrix: for
sum_i b_i=0,

    diag(p^(b_1),...,p^(b_n))
        = product_(r=1)^(n-1) h_rn(p)^(b_r).

Applying the same Smith reduction to an arbitrary element of A now
writes it as a C-diagonal-C product with that diagonal in K. Therefore
K=A. The subgroup C is proper because e_12(1/p) is not integral. This
proves maximality without using p-adic density or a separate elementary-
generation theorem over Z[1/p].

For the word count, D=U g V uses one g letter and D^(-1) uses one
g^(-1) letter. The constructed e_ij(1/p) therefore uses at most
2 p^(m-1) such letters. Signed permutation conjugations and inversion do
not increase this count. The displayed word for h_rs(p) uses only one
fractional transvection, so it has the same bound. A Smith diagonal of
h with exponents b_i consequently gives a word for h containing at most
2 p^(m-1) sum_(r<n)|b_r| occurrences of g or g^(-1). This proves (SPL3).

Finally, for unitaries u,v and e in a finite tracial algebra,

    [e,uv]=[e,u]v+u[e,v],
    ||[e,u^(-1)]||_2=||[e,u]||_2.

Telescope along the word for h. Its C letters contribute zero because
e commutes with pi(C), and every remaining letter contributes at most
||[e,pi(g)]||_2. This proves (SPL2). A nonzero commutator with one h
therefore forces a nonzero commutator with every g outside C.

If e is a projection, E_B(x)=exe+(1-e)x(1-e) for B={e}' cap M. The
off-diagonal corners of x are orthogonal in L^2, so for a unitary x,

    ||E_B(x)||_2^2=1-||[e,x]||_2^2.

Combining this identity with (SPL2) gives (SPL4). This is only a
conditional statement about a leak that already exists.
