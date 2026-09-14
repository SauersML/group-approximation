# Verbatim pins for the torsion lane of Kervaire--Laudenbach (2026-09-13)

Lane `hl-kl-torsion`. Sources fetched on MSI into
`/scratch.global/sauer354/hl-kl-torsion/src/` and
`/scratch.global/sauer354/solve-kl-torsion-car-crash/src/`.

## 1. Klyachko 1993, published PDF

A. A. Klyachko, *A funny property of sphere and equations over groups*,
Comm. Algebra 21(7) (1993), 2555--2575. Read from the publisher PDF (21 pages),
every page rendered. The typography of the scan is reproduced as printed.

- p. 2556: "**C1.** The group K=<G,t; w=1> is not trivial, provided the group
  G is not trivial." and "**Theorem A.** C1 is true, if all the coefficients of
  w have infinite order, in particular, if G is torsion-free."
- p. 2558: "we remark that the condition of infiniteness of coefficients orders
  is actual. The following example due to R. C. Lyndon [11] demonstrates it. The
  equation [a, t^-1 atb]=1 is not solvable over the group
  <a,b; a^3=1, bab^-1=a^2>." (That equation has exponent sum 0, so it concerns
  Theorems B and C, not Theorem A.)
- p. 2565, proof of Theorem 1: "The motion is periodic with the period 2n,
  hence there is a collision in an interior vertex in an integer moment t,
  0 <= t <= 2n. If t != 0, n, then some factor of w has a finite order (Fig.7)."
- p. 2569, Lemma 2 hypotheses: "a_i, b_i, c in H, gp(a_i,P) = <a_i>_inf * P,
  gp(b_i,P^phi) = <b_i>_inf * P^phi, i=0,...,k."
- p. 2571, proof of Lemma 2: "If there is a collision in an interior
  source-vertex (or sink-vertex) (Fig.12), it means a relation in a gp(a_i,P)
  (or gp(b_i,P^phi)). This relation has to be trivial, and the tesselation is
  reducible as usually."
- p. 2572, Lemma 3: "Let w in G*<t>, and the exponent sum of t in w is equal to
  one. Then w is conjugated to a product (prod_{i=0}^k b_i t^-1 a_i t) ct (1)
  were for some m 1) each a_i, b_i, c in P_m 2) each a_i not in P_{m-1}
  3) each b_i not in R_m."
- p. 2573: "**Theorem 4.** The group K=<G,t; w=1> is not trivial, if G is not
  trivial, and each coefficient of w has infinite order." Proof, last lines:
  "(To verify the conditions of Lemma 2 one need to observe the following simple
  fact. If u in (A*B)\A, and each factor of u has infinite order, then
  gp(A,u)=A*<u>_inf.) It is evident, that w(t~)=1. Thus, H~ is an overgroup of G
  containing a solution of (2), hence the natural map G ---> K is a
  monomorphism, and K is non-trivial. Q. E. D."

**Where torsion enters.** The car-crash count (Proposition 1a) uses no
algebra. Torsion enters only through relative freeness: a complete collision
at an interior source or sink vertex reads a relation in `gp(a_i, P)` or
`gp(b_i, P^phi)`, and these subgroups are free products `<a_i> * P` only because
the factors have infinite order. So the hypothesis Klyachko actually needs is
infinite order of the coefficients, not torsion-freeness of `G`.

## 2. Klyachko--Mikheenko (arXiv:2309.09096, `main.tex`)

- l.126--133: "It is easy to see that the system {w_j=1}_{j in J} of equations
  in variables {x_i}_{i in I}=X over G is solvable if and only if
  G cap <<W>> = {1} in G*F(X), where W is the set {w_j}_{j in J} and <<W>> is
  its normal closure in G*F(X)."
- l.139--177: the non-singular definition (rows of exponent sums independent
  over Z), then l.170--177: "The system is called p-nonsingular if the images of
  the words w_j under p-trivialization (i.e. rows of exponent sums of variables
  in w_j modulo p) are linearly independent over Z_p. The system is called
  unimodular if it is p-nonsingular for every prime p."
- l.228--232: "The following conjecture is as yet neither proved nor disproved:
  Howie conjecture [How81]. Any non-singular system of equations over any group
  is solvable."
- l.246--254: "A locally indicable group is a group whose any non-trivial
  finitely generated subgroup admits a surjective homomorphism onto <g>_inf." and
  "A locally p-indicable group for a prime p is a group whose any non-trivial
  finitely generated subgroup admits a surjective homomorphism onto <g>_p."
- l.264--266: "Theorem [How81]. A finite non-singular system of equations over
  a locally indicable group is solvable."
- l.271--274: "Theorem [Kr85]. Let p be a prime. A finite p-nonsingular system
  of equations over a locally p-indicable group is solvable."
- Bibliography: "[Kr85] S. Krstic, Systems of equations over locally
  p-indicable groups, Inventiones mathematicae, 81 (1985), 373--378";
  "[How81] J. Howie, On pairs of 2-complexes and systems of equations over
  groups, J. Reine Angew Math., 1981:324 (1981), 165--174."

Neither Krstic 1985 nor Howie 1981 was read at source here.

## 3. Klyachko 2006 (arXiv:math/0406382v4, `main.tex`)

- Abstract: "A generalized version of the theorem about solvability of
  unimodular equations over torsion-free groups is proved. In a special case,
  this generalized version become a multivariable variant of this theorem."
- Corollary: "An equation g_1 x_{j_1}^{eps_1} ... g_n x_{j_n}^{eps_n}=1 (**)
  over a torsion-free group G with variables x_1,x_2,... is solvable over G if
  prod x_{j_i}^{eps_i} is not a proper power in the free group F(x_1,x_2,...)."

This is one equation in several variables. No theorem read here solves a square
system of several equations over an arbitrary torsion-free group.
