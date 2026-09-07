---
rg: 2
id: certificate-linear-lamp-fourier-compiler-proof
kind: route
title: Represent local certificate predicates by finite lamp idempotents and preserve the inverse defect
target: certificate-linear-counterexamples-compile-to-lamp-algebras
requires:
  - certificate-linear-automata-have-local-linear-decoders
  - stable-finiteness-failure-refutes-surjunctivity
---

## The operator algebra with certificate-dependent coefficients

Let X=B^G and C=C_lc(X,F_p). For s in G define
alpha_s(f)(c)=f(s^(-1).c), where (s.c)(g)=c(s^(-1)g).
The algebraic crossed product R_B consists of finite formal sums f_s u_s
with u_s u_t=u_(st) and u_s f=alpha_s(f) u_s.

Represent it as a family of operators on (F_p)^G by

    (D_f(c)x)(g)=f(g^(-1).c)x(g),
    (R_s x)(g)=x(gs),
    pi_c(f u_s)=D_f(c) R_s.

The identity R_s D_f(c)=D_(alpha_s(f))(c) R_s verifies the crossed-product
relation; R_s R_t=R_(st). The family is faithful: if sum_s D_(f_s)(c) R_s
vanishes for every c, evaluating at g=1 and independently varying the
input values x(s) forces f_s(c)=0 for every s,c. The same argument works
for matrices. No freeness assumption on the action on X is needed.

The local data rule T_c corresponds to a matrix A in M_n(R_B).
By the decoder lemma there is B_0 in M_n(R_B) with pi_c(B_0)=S_c and
S_c T_c=I for all c. Faithfulness gives B_0 A=I. Nonsurjectivity of E
means some T_c is not onto, because the certificate is retained. For that
c, T_c S_c cannot be I. Hence A B_0!=I in M_n(R_B).

Conversely, a pair B_0 A=I with A B_0!=I in M_n(R_B) gives injective T_c
for every c. Faithfulness detects A B_0-I in at least one fiber; in that
fiber T_c cannot be onto, since a surjective map with a left inverse has
that map as a right inverse too. This proves the stated stable-finiteness
equivalence for R_B.

## Encode every certificate by characters of finite lamps

Choose L=(C_2)^a, K=F_p when p is odd, and L=(C_3)^a, K=F_4 when p=2,
with |L|>=|B|. In either case p does not divide |L| and K contains all
characters of L. Let Lhat=Hom(L,K^x), so |Lhat|=|L|. Choose any onto map
rho:Lhat->B and extend it coordinatewise to an equivariant surjection

    q:Y=Lhat^G -> X=B^G.

Pullback f->f composed with q, followed by inclusion of F_p into K, embeds
C equivariantly and unitally into C_lc(Y,K). It therefore embeds R_B into
C_lc(Y,K) semidirect G: the distinct formal group terms remain distinct,
and surjectivity of q makes coefficient pullback injective. In particular
the reverse defect stays nonzero. No approximation or limiting measure
is involved in this step.

## Fourier transform is a finite algebraic identity on each support

Set Lambda=direct_sum_G L. Define

    F:K[Lambda] -> C_lc(Y,K),
    F([lambda])(z)=product_(g in supp(lambda)) z(g)(lambda(g)).

On a finite set H of sites this is the usual Fourier isomorphism
K[L^H] -> K^(Lhat^H). Its inverse on a one-site character indicator is

    1_{z(g)=chi}  <->  |L|^(-1) sum_(l in L) chi(l)^(-1)[l at g].

Indeed evaluation at a character psi sums the character psi chi^(-1)
over L, giving 1 for psi=chi and 0 otherwise. Products give all finite
pattern indicators. Taking the union over finite H gives an isomorphism
onto the locally constant functions: compactness implies that every such
function depends on finitely many sites. The character basis on each
finite H also proves injectivity.

For the shift action s.lambda at g equal to lambda(s^(-1)g), direct
substitution gives F([s.lambda])=alpha_s(F([lambda])). Thus Fourier
extends to an algebra isomorphism

    K[(direct_sum_G L) semidirect G]
       ~= C_lc(Y,K) semidirect G.

Combining the preceding embeddings places the inverse pair faithfully in
M_n(K[W]). In odd characteristic this is already the asserted prime-field
pair. In characteristic two, represent multiplication by each element of
F_4 on its two-dimensional F_2-vector space. The resulting unital injection
F_4->M_2(F_2) extends coefficientwise to

    M_n(F_4[W]) -> M_(2n)(F_2[W]).

It preserves both B_0 A=I and A B_0!=I. Applying
stable-finiteness-failure-refutes-surjunctivity proves nonsurjunctivity of W.

## Scope of the computational translation

Every finite predicate on the certificate is a sum of finite-pattern
indicators. The displayed Fourier formula therefore translates arbitrary
finite verification logic in the coefficients, not only literal bit tests.
Each data output may be a sum of several inputs with these coefficients.
All expressions still have finite group-algebra support.

For a rule (T_c x+b(c),sigma(c)), where sigma is a reversible certificate
CA independent of x, first apply sigma^(-1) to the output certificate and
then subtract b(c) from its data. These are reversible local operations and
reduce injectivity and nonsurjectivity to those of (T_c x,c).

The reduction does not prove that a suitable T exists. Nor does it extend
a decoder valid only on a proper certificate subshift to arbitrary garbage:
the decoder lemma uses injectivity for all c in the entire compact full
shift, and the faithful pullback uses the onto map q onto that full shift.
It also supplies no unwarranted transfer of stable finiteness from G to W.

The Fourier construction is the standard one, with the splitting-field
hypotheses made explicit; see Ara--Claramunt, Proposition 5.8,
https://arxiv.org/abs/2005.12374. The local decoder has the related NUCA
precedent recorded at certificate-linear-automata-have-local-linear-decoders.
