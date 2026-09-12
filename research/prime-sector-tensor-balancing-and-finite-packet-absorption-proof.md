---
rg: 2
id: prime-sector-tensor-balancing-and-finite-packet-absorption-proof
kind: route
title: Balance one prime central sector and absorb it in a finite packet
target: prime-cyclic-finite-packet-amalgams-reflect-the-source-hs-gap
requires:
  - finite-central-hs-sector-decomposition
  - amenable-edge-cycles-cannot-create-an-lcs-gap
---

# Balance one prime central sector and absorb it in a finite packet

## 1. Normal form and exact finite-dimensional representations

Let \(q=|z|\). In

\[
 B=K\rtimes_\alpha\langle r\rangle,\qquad r^p=1,
\]

the subgroup \(\langle r,z\rangle\) is \(C_p\times C_q\): the two
elements commute because \(\alpha(z)=z\), and the semidirect-product
normal form gives trivial intersection. The same group embeds in

\[
 D=E\times\langle z\rangle
\]

as \(\langle c,z\rangle\). Hence the amalgam

\[
 \Pi=B*_{C_p\times C_q}D                              \tag{1}
\]

is defined by injective edge maps. Its standard normal form embeds both
vertices. In particular, \(z\ne1\) in \(\Pi\). It is central in both
vertices and belongs to the common edge, so

\[
 z\in Z(\Pi),\qquad z\ne1.                              \tag{2}
\]

Finite presentations of \(E\) and \(K\), the relations
\(rkr^{-1}=\alpha(k)\) on a finite generating set of \(K\), and the two
edge identifications give a finite presentation of \(\Pi\).

Suppose now that every finite-dimensional representation of \(E\) kills
\(c\). If \(\pi:\Pi\to U(d)\) is finite-dimensional, then
\(\pi(c)=I\). The semidirect relations give

\[
 \pi(\alpha(k))=\pi(k)\qquad(k\in K).                   \tag{3}
\]

Thus \(\pi|_K\) factors through the coinvariant quotient \(K_\alpha\).
The hypothesis \(z=1\) in \(K_\alpha\) gives \(\pi(z)=I\).

## 2. Hyperlinearity is reflected

If \(E\) is hyperlinear, so is \(D=E\times C_q\). The group \(B\) is
finite and the edge in (1) is finite, hence amenable. Amenable-edge
permanence makes \(\Pi\) hyperlinear.

Conversely, \(E\leq D\leq\Pi\) by normal form, and subgroups of
hyperlinear groups are hyperlinear. Therefore

\[
 E\text{ hyperlinear}\quad\Longleftrightarrow\quad
 \Pi\text{ hyperlinear}.                                \tag{4}
\]

This part needs no representation stability and no property (T).

## 3. A finite proof in the coinvariant quotient gives an HS modulus

Choose a finite generating set \(T\) of \(K\). Since \(z=1\) in
\(K_\alpha\), there is a fixed identity in \(K\)

\[
 z=
 \prod_{\nu=1}^{N}
 h_\nu\bigl(\alpha(k_\nu)k_\nu^{-1}\bigr)^{\epsilon_\nu}
 h_\nu^{-1},
 \qquad \epsilon_\nu\in\{1,-1\},                        \tag{5}
\]

for fixed \(T\)-words \(h_\nu,k_\nu\). This is simply a finite witness
that \(z\) belongs to the normal closure in (1) of the coinvariant
differences.

Fix the resulting finite presentation of \(\Pi\). Let a unitary tuple
have maximum normalized-HS relator defect at most \(\delta\), and write
\(C\) for the evaluated actor word \(c\). Word telescoping through the
fixed \(K\)-relators and the finitely many semidirect relators gives
constants \(L_\nu,M<\infty\) such that

\[
 \|\alpha(k_\nu)(T)-Ck_\nu(T)C^*\|_2\leq L_\nu\delta
\]

and the evaluated two sides of (5) differ by at most \(M\delta\).
Moreover,

\[
 \|Ck_\nu(T)C^*-k_\nu(T)\|_2\leq2\|C-I\|_2.
\]

Conjugation and multiplication by unitaries preserve normalized HS norm,
so telescoping the \(N\) factors in (5) yields constants \(A,B\),
independent of matrix dimension, for which

\[
 \|Z-I\|_2\leq A\|C-I\|_2+B\delta.                      \tag{6}
\]

Consequently collapse of \(c\) in every HS almost representation of
\(E\) implies collapse of \(z\) in every HS almost representation of
\(\Pi\).

## 4. One nontrivial prime sector generates all sectors

Assume collapse of \(c\) fails. Finite central HS sector decomposition
gives, after a subsequence and compression to a positive-density block,
unitary \(E\)-tuples \(U_n\) such that

\[
 \operatorname{Def}_E(U_n)\longrightarrow0,\qquad
 U_n(c)=\omega^j I,\quad
 \omega=e^{2\pi i/p},\quad j\ne0.                       \tag{7}
\]

For a fixed positive integer \(k\), send each presentation generator to
its \(k\)-fold tensor power. Every relator value becomes the \(k\)-fold
tensor power of its old value, and

\[
 \|V^{\otimes k}-I\|_2\leq k\|V-I\|_2.                 \tag{8}
\]

Thus \(U_n^{\otimes k}\) still has defect tending to zero, while its
central value is \(\omega^{jk}I\).

Because \(p\) is prime, \(j\) generates \(\mathbb Z/p\mathbb Z\). For
each \(\ell\ne0\), choose \(1\leq k_\ell<p\) with
\(jk_\ell=\ell\pmod p\), and use \(U_n^{\otimes k_\ell}\) for sector
\(\ell\). Use the trivial exact representation of \(E\) for sector zero.
By taking direct-sum multiples, make all \(p\) sector dimensions equal
to one common number \(M_n\). Enlarging \(M_n\) by any fixed factor is
harmless. The direct sum \(V_n\) then satisfies

\[
 \operatorname{Def}_E(V_n)\longrightarrow0,\qquad
 V_n(c)\text{ has every }p\text{-th root with multiplicity }M_n.
                                                               \tag{9}
\]

## 5. The finite regular block has the same balanced edge spectrum

Choose a nontrivial character \(\zeta\) of \(\langle z\rangle\).
Inside the left regular representation of the finite group \(B\), take
the central \(\zeta\)-spectral subspace

\[
 {\cal H}_\zeta
 =
 \operatorname{ran}\left(
 \frac1q\sum_{a=0}^{q-1}\overline{\zeta(z)^a}\,
 \lambda_B(z)^a\right).                                 \tag{10}
\]

Let \(\tau_\zeta\) be the resulting representation of \(B\). It has

\[
 \tau_\zeta(z)=\zeta(z)I.                               \tag{11}
\]

Its restriction to \(\langle r\rangle\) is a multiple of the regular
representation of \(C_p\). Indeed, for \(1\leq k<p\),

\[
 \operatorname{Tr}_{{\cal H}_\zeta}(\tau_\zeta(r^k))=0, \tag{12}
\]

because the regular trace of every \(z^a r^k\) is zero: semidirect-product
normal form says \(z^a r^k\ne1\). Fourier inversion on \(C_p\) now gives
equal multiplicity for every \(p\)-th root of unity.

Choose the common multiplicity \(M_n\) in Section 4 to be divisible by
this fixed multiplicity. A direct-sum multiple of \(\tau_\zeta\) then
has exactly the same \(r\)-spectrum as \(V_n(c)\). After one unitary
change of basis, arrange

\[
 \tau_\zeta(r)=V_n(c).                                  \tag{13}
\]

Use this conjugated finite \(B\)-representation for the \(K\)-generators,
use \(V_n\) for the \(E\)-generators, and send the common \(z\) to the
scalar \(\zeta(z)I\). The two vertex tuples agree exactly on the edge.
Every \(B\)-relation and every edge relation is exact; only the
vanishing \(E\)-defects remain. Hence these are \(\Pi\)-tuples with

\[
 \operatorname{Def}_\Pi\longrightarrow0,\qquad
 \|Z-I\|_2=|\zeta(z)-1|>0.                              \tag{14}
\]

Thus collapse of \(z\) implies collapse of \(c\). Together with (6), this
proves the equivalence of HS collapse.

## 6. Scope

The proof uses three features and no hidden stability theorem:

1. the selector packet \(K\) is fixed and finite;
2. the actor mark has prime order, so one nontrivial sector tensor-generates
   every central sector; and
3. the interface is the literal finite-edge normal-form amalgam (1).

The shared-center extraspecial construction evades item 1 by demanding
arbitrarily many independent Pauli pairs. A genuinely non-Bass--Serre
interface may evade item 3. But within the stated class, property (T),
finite-dimensional image collapse, and a nonlinear finite selector do
not amplify the source gap at all. No nonhyperlinear group is constructed
here.
