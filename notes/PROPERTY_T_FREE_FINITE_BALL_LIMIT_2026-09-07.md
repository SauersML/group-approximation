# A finite-ball limit on relation-energy proofs

Date: 2026-09-07.

## Status and scope

This note records an elementary proved obstruction to one proposed way of
removing property (T) from a non-MF proof. It does **not** provide a
property-(T)-free non-MF group, refute the possibility of such a proof, or
change the manuscript's theorem dependencies. No literature-level novelty
or Lean verification is claimed for the observation below.

The investigation excluded binary self-similarity, reuse of existing Cairn
arguments as a new proof, and cancellation of first-order relation errors
after passage to a smaller model. It also excluded the recent Eckhardt
non-MF argument. The proof here uses only extension of partial permutations.
The Cairn entries accompanying this note archive its precise mathematical
content; they do not supply an existence theorem.

## Finite permutation models on one vector

**Proposition.** Let

$$G=\langle s_1,\ldots,s_m\mid R\rangle.$$

For every finite set of relator words $R_0\subseteq R$ and every word $w$
with $w\ne 1$ in $G$, there are permutation matrices $U_1,\ldots,U_m$
of a common finite size and a unit vector $\xi$ such that

$$r(U)\xi=\xi\quad(r\in R_0),\qquad
  \|(w(U)-I)\xi\|=\sqrt{2}.$$

No finite-presentability assumption is needed.

**Proof.** Give $G$ the word metric for the symmetric generating set
$\{s_i^{\pm1}\}$. Choose $L$ at least the lengths of all the specified
words, and let $B_L$ be the finite ball about $1_G$.

For each $i$, define a partial permutation of $B_L$ by

$$g\longmapsto s_i g\quad\text{whenever }g,s_i g\in B_L.$$

It is a bijection from its domain to its range. Their complements in
$B_L$ have equal finite cardinality, so it extends to a permutation
$\sigma_i$ of $B_L$. Let $U_i\delta_g=\delta_{\sigma_i(g)}$ on
$\ell^2(B_L)$ and set $\xi=\delta_{1_G}$.

The inverse $U_i^{-1}$ also agrees with left multiplication by $s_i^{-1}$
whenever both endpoints lie in $B_L$. When a word $q$ of length at most
$L$ is applied to $\xi$, its letters act from right to left; every
intermediate point is represented by a suffix of $q$, hence lies in
$B_L$. Therefore

$$q(U)\xi=\delta_{q_G},$$

where $q_G$ is the element represented by $q$. A relator gives
$\delta_{1_G}$; $w$ gives the orthogonal vector $\delta_{w_G}$. This
proves the assertion. $\square$

This is an existence argument using a finite subset of $G$, not an
algorithm for computing that subset from an arbitrary presentation with
an undecidable word problem. It does not assert that the completed
permutations are an approximate representation in operator norm.

## Consequence for operator-order estimates

**Corollary.** With $R_0$ and $w$ as above, there is no $C\geq0$ such
that every finite-dimensional unitary tuple satisfies

$$
(w(U)-I)^*(w(U)-I)
\ \leq\ C\sum_{r\in R_0}(r(U)-I)^*(r(U)-I).
$$

Here $\leq$ denotes the order on self-adjoint matrices.

**Proof.** Evaluate the alleged inequality on the vector supplied by the
proposition. Its left-hand quadratic form is $2$ and its right-hand
quadratic form is $0$. $\square$

Equivalently, a universal estimate controlling
$\|(w(U)-I)\xi\|$ by the relation errors on that same vector cannot
hold. This excludes a direct relation-Laplacian domination argument of
the displayed form. It does not exclude every argument involving a
Laplacian, auxiliary hypotheses, or global norm bounds.

## The global norm distinction

The corollary does **not** rule out an inequality between scalar norms,

$$\|w(U)-I\|\leq C\max_{r\in R_0}\|r(U)-I\|.$$

Our construction fixes the relators on one vector, but leaves their
action on other vectors uncontrolled. In particular, it supplies no
bound tending to zero for the full operator-norm relation defects.

A sufficient target for an independent non-MF argument remains: find
$G$, $w\ne1$ in $G$, a finite $R_0\subseteq R$, and $\eta>0$ such that
in every matrix dimension

$$
\max_{r\in R_0}\|r(U)-I\|<\eta
\quad\Longrightarrow\quad \|w(U)-I\|<1.
$$

If $G$ were MF, its finite matrix models could satisfy the given
relations arbitrarily well while keeping $w$ at distance at least $1$
from the identity, by the uniform separation characterization. Thus the
displayed implication would contradict MF. See Korchagin, Propositions
7–8, in [MF-property for countable discrete groups](https://arxiv.org/html/1704.06906v3).

The finite-ball proposition does not prove this implication for any
candidate. It identifies why passing from vector estimates to a global
operator-norm conclusion requires additional mathematics.

## Literature checks and limits of the search

The following checks concern the routes investigated in this session;
they are not an exhaustive assertion about the current literature.

1. **Conjugation to powers.** The Baumslag group
   $\langle a,b\mid a^{a^b}=a^2\rangle$, with $x^y=y^{-1}xy$, is MF.
   Consequently this relation by itself cannot be used as a non-MF
   obstruction. See [Korchagin, §3](https://arxiv.org/html/1704.06906v3).
2. **Quantum games.** A general failure of Connes embedding cannot simply
   be substituted for a group obstruction. The passage from general
   constraint-game algebras to the linear-system setting associated with
   group algebras is a substantive additional step. See
   [Slofstra, The algebraic side of MIP*=RE (2020)](https://simons.berkeley.edu/sites/default/files/docs/15568/williamslofstraslides-quantumprotocols.pdf).
   This historical source explains the distinction; it is not evidence
   that every related problem remains open in 2026.
3. **Norm conventions.** The MF notion here is embedding a group into
   the unitary group of a norm matrix corona. Operator-norm separation
   need not survive passage to normalized Hilbert–Schmidt norm, so the
   inequality between the two norms is not a proof that this MF notion
   implies hyperlinearity. Korchagin's introduction makes this distinction
   explicitly.

The outcome of this investigation is the proposition and corollary above,
together with an unresolved global norm step. It supplies no basis for
removing property (T) from the manuscript or for merging its proof with
the AH $K_1$ construction.

## Repository integration

- [Finite-ball claim](../research/finite-ball-permutations-realize-word-orbits.md)
  and [direct proof route](../research/finite-ball-permutations-realize-word-orbits-proof.md).
- [Operator-order obstruction](../research/nontrivial-words-have-no-relation-energy-domination.md)
  and [proof route](../research/nontrivial-word-energy-domination-no-go-proof.md).

These entries establish only the stated finite-model fact and its
operator-order consequence. They do not mark a property-(T)-free
existence target solved or attach formal verification claims.
