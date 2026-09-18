---
rg: 2
id: bors-embedding-is-effective-in-the-machine-citation
kind: route
title: Import BORS Theorem 1.1 and Lemma 4.35 and read uniformity from the explicit S-machine and H_N(S) constructions
target: bors-embedding-is-effective-in-the-machine
requires: []
---

Literature import, read from source 2026-09-17.  Sources: J.-C. Birget,
A. Yu. Ol'shanskii, E. Rips, M. V. Sapir, *Isoperimetric functions of groups
and computational complexity of the word problem*, arXiv:math/9811106 (BORS);
M. V. Sapir, J.-C. Birget, E. Rips, *Isoperimetric and isodiametric functions
of groups*, arXiv:math/9811105 (SBR).  Quotations are transcribed from the
arXiv PDFs; mathematical symbols are rendered in plain text.

## 1. Existence and metric bounds (BORS Theorem 1.1)

> "Let G be a finitely generated group with word problem solvable by a
> non-deterministic Turing machine with time function <= T(n) such that
> T(n)^4 is superadditive (that is T(m+n)^4 >= T(m)^4 + T(n)^4 for every
> m, n). Then G can be embedded into a finitely presented group H with
> isoperimetric function equivalent to n^2T(n^2)^4 in such a way that G has
> bounded distortion in H. In particular, the word problem of a finitely
> generated group is in NP if and only if this group is a subgroup of a
> finitely presented group with polynomial isoperimetric function."

The time function is the one of the SBR Introduction:

> "For every natural number n let T(n) be the smallest number such that for
> every acceptable word w with |w| <= n there exists a computation of length
> <= T(n) which accepts w."

"Solvable by" means acceptance of the trivial words, BORS Section 2.2: "Let
S = S(M). Then S also solves the word problem in G in the following sense. For
every group word u in the alphabet A, the word u is equal to 1 in G if and only
if the S-machine S takes the word sigma(c(u)) to W0".

## 2. The procedure (BORS, Introduction)

> "Using the proof of Theorem 1.1, in order to embed a finitely generated group
> with word problem in NP into a finitely presented group with polynomial
> isoperimetric function, one needs first construct a Turing machine which
> solves the word problem, then convert it into an S-machine, then convert the
> S-machine into a group."

## 3. Machine to S-machine (SBR Sections 3--4)

SBR, before Lemma 3.1: "In the next section we will show how to convert any
Turing machine to an S-machine".  Lemma 3.1 replaces `M` by a symmetric machine
`M'` recognizing the same language with equivalent time function.  Later in SBR
Section 4: "Now we are ready to take any Turing machine M = <X,Y,Q,Theta,s1,s0>
satisfying the conditions of Lemma 3.1 and to construct an S-machine S(M)
simulating M."  The state letters and the rules of `S(M)` are then listed
("Now let us describe the set of rules of S(M). It will consist of the rules of
S4(tau), S9(tau), S_alpha(tau), S_omega(tau) for all tau of the form (22) plus
the following connecting rules"), one block per command `tau` of `M'`.

## 4. S-machine to group (BORS Sections 2--3 and 7)

BORS Section 2.2 fixes the parameter: "fix a large natural number N. Up to
Section 7 it will be enough to assume that N >= 9, the exact value of N will be
given in Section 7."  Section 7.1: "Let us fix N = 9ck where c is the constant
from Lemma 4.33 (notice that c is twice the maximal number of Y letters in
relations of the finite presentation of GN(S) and does not depend on N) and k
is the number of components of the vector Q of the S-machine S."

BORS Section 3:

> "The set of generators of HN(S) consists of all the generators of GN(S),
> together with the following new letters: rho, d, and the set B which is in
> one-to-one correspondence with the set A (we assume that this correspondence
> preserves inverses)."

followed by the explicit relations (commutation of `rho` with the listed
letters, `rho^-1 kappa_1 rho = kappa_1 d^-1`, `rho^-1 kappa_2 rho = d kappa_2`,
`d^-1 a_i d = a_i b_i`, and `a_i b_j = b_j a_i`), and

> "Let Gb be the copy of G over the generating set B ... We will show later
> (see Lemma 4.35 below) that the identity map on B induces an isomorphism
> between Gb and the subgroup <B> of H."

BORS Lemma 4.35: "The homomorphism from Gb onto the subgroup <B> induced by the
identity map on B (see Lemma 3.1) is an isomorphism."

## Reading

The inputs of Sections 3 and 4 are finite: the command list of `M`, then the
rule list of `S(M)`, then the integer `N = 9ck`, where `c` and `k` are read off
the finite presentation of `G_N(S)` and the hardware of `S`.  The presentation
`H_N(S)` is a finite list of words in these letters.  The relations of `G` are
never used as relations of `H_N(S)`; `G` enters only through the language that
`S` accepts.  Hence `M -> (P(M), (b_x)_x)` is computable, with `b_x` the letter
of `B` corresponding to `x`, and Theorem 1.1 with Lemma 4.35 supplies the
conditional conclusions.
