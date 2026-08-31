---
rg: 2
id: decidable-word-problem-hyperlinear-microstate-search-proof
kind: route
title: Enumerate rational Cayley unitaries and stop at the first strict canonical profile
target: decidable-word-problem-hyperlinear-has-computable-canonical-microstate-modulus
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

Fix (n,q). The word-problem algorithm partitions the finite list of freely
reduced words of length at most (n) into the two classes occurring in
((mathrm{CHM1})).

## 1. A computable dense family of exact unitaries

Enumerate dimensions (d) and (m)-tuples of skew-Hermitian matrices

[
 K_iin M_d(mathbb Q(i)),qquad K_i^*=-K_i.
]

For each one form its Cayley transform

[
 U_i=(I-K_i)(I+K_i)^{-1}.                                	ag{CHP1}
]

The matrix (I+K_i) is invertible because a skew-Hermitian matrix has purely
imaginary spectrum. Hence (U_i) is an exact unitary with entries in
(mathbb Q(i)). Rational skew-Hermitian matrices are dense, the Cayley
transform parametrizes the unitaries without eigenvalue (-1), and that
latter set is dense in (U(d)). Thus these tuples form a computable dense
subset of (U(d)^m) in every dimension.

For a tuple in this enumeration, every entry of every (w(U)) lies in
(mathbb Q(i)). Both

[
 |w(U)-I|_{2,d}^2
 quad	ext{and}quad
 |operatorname{tr}_d(w(U))|^2                         	ag{CHP2}
]

are rational numbers. The strict tests in ((mathrm{CHM1})) are therefore
decidable by exact integer arithmetic after clearing denominators.

Dovetail the enumerations over all (d) and all rational Cayley tuples, and
stop at the first tuple passing every test. This is a partial computable
search with the advertised output type.

## 2. Hyperlinearity makes the search total

By
`hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`, hyperlinearity
of (Gamma) supplies finite-dimensional unitary tuples whose moments on any
prescribed finite word set converge to the canonical group trace

[
 	au_Gamma(w)=
 egin{cases}
 1,&w=_{Gamma}1,\
 0,&w
e_{Gamma}1.
 end{cases}                                             	ag{CHP3}
]

For a trivial word, convergence of its trace to (1) is equivalent to
convergence to (I) in normalized Hilbert--Schmidt norm, since for a
unitary (V),

[
 |V-I|_{2,d}^2=2-2operatorname{Re}operatorname{tr}_d(V). 	ag{CHP4}
]

Choose such a tuple satisfying all the finite tests with error strictly
smaller than (2^{-(q+2)}). Word evaluation, normalized trace, and normalized
Hilbert--Schmidt norm are continuous on the compact finite product
(U(d)^m). A sufficiently close rational Cayley tuple therefore still
satisfies every test with error strictly below (2^{-q}). The dovetailed
search eventually reaches it and halts.

Let (d(n,q)) be the returned dimension and put

[
 mu_{Gamma,W}(n,q)
   =max{d(i,j):1le ile n, 1le jle q}.             	ag{CHP5}
]

Only finitely many total searches occur, so this is total computable and
nondecreasing. The witness for ((n,q)) has dimension at most
(mu_{Gamma,W}(n,q)), proving ((mathrm{CHM3})).

## 3. Ball-table conversion

For (g,h,ghin B_R), choose representative words of length at most (R).
Then

[
 w_gw_hw_{gh}^{-1}=_{Gamma}1
]

has length at most (3R), so its ((3R,q))-test is exactly the
multiplication defect after multiplication on the right by the unitary
(w_{gh}(U)). If (g
e h), the word
(w_g^{-1}w_h) is nontrivial and has length at most (2R); applying its
trace test gives ((mathrm{CHM4})). This proves the effective conversion to
the usual local definition.

No presentation relator enumeration, Dehn function, stability theorem, or
rounding to an exact representation is used.
