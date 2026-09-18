---
rg: 2
id: fg-subrings-of-integral-form-algebras-omit-q
kind: claim
title: A finitely generated subring of an algebra with finitely generated structure constants contains no copy of Q
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the root embedding problem for the group GL_n(Q); this is a ring-level obstruction that removes one family of coefficient rings from the routes to it.
  leavitt-subalgebra-linear-groups-satisfy-boone-higman: that embeds GL_n(A) in the binary Leavitt unit group for unital subalgebras A of L_{F_2}(1,2); this shows that in characteristic 0 no finitely generated subring of any Leavitt algebra can contain Q, so GL_n(Q) is never reached that way.
---

**ESTABLISHED** through `fg-subrings-of-integral-form-algebras-omit-q-proof`
(lane proof, not independently reviewed).

**Statement.** Let `K` be a field of characteristic 0 and `B` a `K`-algebra with a
`K`-basis `(b_j)_{j in J}` such that all structure constants `c^l_{ij}`
(`b_i b_j = sum_l c^l_{ij} b_l`) and all coordinates of `1` lie in one finitely
generated subring `A_1 <= K`. Let `S <= B` be a finitely generated subring, unital or
not, and `m >= 1`. Then:
1. every nonzero element of `M_m(S)` is divisible in `M_m(S)` by only finitely many
   primes `p` (that is, `x = p y` with `y in M_m(S)` for only finitely many `p`);
2. so `(M_m(S), +)` contains no nonzero divisible subgroup, and there is no nonzero
   ring homomorphism `Q -> M_m(S)`, unital or not. In particular no corner
   `e M_m(S) e` contains a copy of `Q`;
3. so `(Q,+)` has no embedding into `GL_m(S)` of the form `q -> 1 + N(q)` with `N`
   additive. This covers the elementary unipotents `e_ij(q)`, and so every
   embedding `GL_n(Q) -> GL_m(S)` induced by a ring homomorphism `M_n(Q) -> M_m(S)`.

**Examples of such `B`** (structure constants in `Z` for a monomial basis):
Leavitt path algebras `L_K(E)` of arbitrary graphs, including `L_K(1,n)`, and Cohn
path algebras (normal-form bases); group algebras `K[Gamma]`; Weyl algebras;
enveloping algebras of Lie algebras with integral structure constants; every
finite-dimensional `K`-algebra (finitely many constants). In characteristic `p > 0`
no ring of characteristic `p` contains `Q` at all.

**Consequences for the root `gl-n-q-embeds-in-fp-simple-group`.**
- **Leavitt coefficient route closed.** No finitely generated subring of `L_K(1,2)`,
  over any field `K`, contains `Q`. So the step "`GL_n(Q) <= GL_n(A) <= L^x` for a
  finitely generated subring `A`" cannot occur inside a Leavitt, Cohn, group,
  Weyl or finite-dimensional algebra. A finitely generated coefficient ring carrying
  `Q` must lie outside every such algebra: its multiplication has to create
  denominators at infinitely many primes. An example of the needed kind is an operator
  such as `D = 1/(1 + number of leading ones)` adjoined to the Leavitt operators on a
  space of functions, whose products have unbounded denominators.
- **What is not settled here: group-level embeddings.** Every finitely generated
  subgroup of `U(L_K(1,2))` lies in `U(L_A(1,2))` for a finitely generated subring
  `A <= K`, since its generators and their inverses have coordinates in one such
  `A`. Whether `U(L_A(1,2))` can contain `(Q,+)` by means that are not ring-linear
  is left open. The obvious reduction modulo the maximal ideals of `A` fails,
  because `V <= U(L_F(1,2))` (via the permutation units `sum_i x_{beta_i} y_{alpha_i}`)
  already contains the divisible group `Q/Z` (survey Theorem 4.3(3)).
