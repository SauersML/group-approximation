---
rg: 2
id: bass-serre-two-selector-leakage-proof
kind: route
title: Rewrite the relative selector, apply Britton normal form, and compute every fibre block
target: two-qutrit-selectors-have-virtually-free-holonomy
requires:
  - qutrit-full-leavitt-prefix-conjugator-realizes-phase-star
  - qutrit-matched-prefix-router-family-is-one-finite-hnn-chart
---

Set \(c=vu^{-1}\), so \(v=cu\). The second selector relation in
(TSH1) becomes

\[
 vJv^{-1}=c(uJu^{-1})c^{-1}=chc^{-1}=h.
\]

This proves the Tietze equivalence (TSH2). In Bass--Serre language there
is one finite vertex group \(F\). One loop edge identifies
\(\langle J\rangle\) with \(\langle h\rangle\) through \(u\), and the
other loop edge identifies \(\langle h\rangle\) with itself through
\(c\). Both edge groups have order three. A finite graph of finite groups
has a free subgroup of finite index, so \(\Lambda_2\) is virtually free.
It is therefore residually finite.

Britton normal form for the \(c\)-loop shows that every word

\[
 h^j c^k,\qquad k\ne0,
\]

is nontrivial. In particular \(c\) has infinite order and

\[
 \langle h,c\rangle\cong C_3\times\mathbb Z.             \tag{BTS1}
\]

The same normal form gives the exact intersection. If \(a\in C\) and
\(cac^{-1}\in C\subset F\), then the stable-letter word can reduce only
when \(a\in\langle h\rangle\). Conversely \(c\) centralizes every element
of \(\langle h\rangle\). Hence

\[
 C\cap cCc^{-1}=\langle h\rangle.                       \tag{BTS2}
\]

Applied to the two original loop edges, the identical argument gives

\[
 C\cap uCu^{-1}=C\cap vCv^{-1}=\langle h\rangle,         \tag{BTS3}
\]

where the corresponding source edge subgroup is \(\langle J\rangle\).

We now compute in the canonical group trace. For a character
\(\chi_{a,b}\) of \(C\), write \(p_{a,b}\) for its minimal character
projection. The finite-subgroup double-coset calculation says that for
\(g\in\Lambda_2\),

\[
 \|p_{\chi'}g p_\chi\|_2^2
 =\frac{|C\cap gCg^{-1}|}{|C|^2}                        \tag{BTS4}
\]

when the two characters agree after transport on the intersection, and
the block is zero otherwise. Indeed, expanding both character projections
in the group basis leaves exactly one term for every element of the
intersection; incompatible character phases sum to zero.

For \(g=c\), transport fixes \(h\). Since

\[
 \chi_{a,b}(h)=\omega^{2a+b},
\]

equations (BTS2) and (BTS4) give

\[
 \|p_{a',b'}c p_{a,b}\|_2^2
 =\frac3{9^2}=\frac1{27}
\]

exactly when \(2a'+b'=2a+b\), and zero otherwise. This proves
(TSH4).

Let \(r_\ell\) be the \(\omega^\ell\)-spectral projection of \(h\).
It is a linear combination of \(1,h,h^2\). Equation (BTS1) says that
none of the group elements \(h^jc^k\), with \(k\ne0\), is the identity.
The canonical trace therefore gives

\[
 \tau(r_\ell c^k)=0\quad(k\ne0).                         \tag{BTS5}
\]

Since \(c\) commutes with \(r_\ell\), \(\tau(r_\ell)=1/3\), and
\(\tau(r_\ell c)=0\),

\[
 \begin{aligned}
 \|(c-\zeta)r_\ell\|_2^2
 &=\tau\!\left(r_\ell(c-\zeta)^*(c-\zeta)\right)\\
 &=2\tau(r_\ell)
   -2\operatorname{Re}\!\left(\overline\zeta\,
      \tau(r_\ell c)\right)
 =\frac23 .
 \end{aligned}                                          \tag{BTS6}
\]

This proves (TSH5).

For \(W=u\) or \(W=v\), character compatibility in (BTS3) is

\[
 \chi_{a',b'}(h)=\chi_{1,b}(J)=\omega.
\]

Thus for every source atom \(e_b=p_{1,b}\), exactly the three target
atoms

\[
 p_{1,2},\qquad p_{0,1},\qquad p_{2,0}                  \tag{BTS7}
\]

are allowed, and each corresponding block has squared norm \(1/27\).
Put \(q=e_0+e_1+e_2\). Since \(WqW^{-1}=r_1\) and
\(qr_1=p_{1,2}\), orthogonality of the character blocks yields

\[
 \|qWq\|_2^2=3\cdot\frac1{27}=\frac19.
\]

Therefore

\[
 \|(1-q)Wq\|_2^2
 =\|Wq\|_2^2-\|qWq\|_2^2
 =\frac13-\frac19=\frac29.                              \tag{BTS8}
\]

For \(R=e_0+e_1\), only two source atoms occur, so

\[
 \|qWR\|_2^2=\frac2{27},\qquad
 \|(1-q)WR\|_2^2=\frac29-\frac2{27}=\frac4{27}.          \tag{BTS9}
\]

The same sum over the three source atoms shows that each target in
(BTS7) receives squared mass \(1/9\) from \(Wq\). This proves (TSH6)
and the exact hidden-sector assertion.

Finally fix a word radius \(L\). There are only finitely many nonidentity
group elements whose vanishing traces enter the expansions above and the
moments of words of length at most \(L\). Residual finiteness supplies one
finite quotient in which all of them remain nonidentity; include every
nonidentity element of \(F\) in this finite list, so the quotient is
injective on \(F\). Its left regular representation has trace zero on
each listed nonidentity element and trace one on the identity. It therefore
matches the canonical trace on the whole chosen window and realizes every
presentation relation exactly.

For concrete prefix matrices, both intertwinings

\[
 DN_J=N_hD,\qquad D'N_J=N_hD'
\]

imply that \(D'D^{-1}\) centralizes \(N_h\). After the scalar normal-form
change this is precisely the relation \([g'g^{-1},h]=1\) modeled above.
Any further relation of the actual coefficient matrix is extra information;
the two selector rows and their relative holonomy alone do not contain it.
