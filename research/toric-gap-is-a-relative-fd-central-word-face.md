---
rg: 2
id: toric-gap-is-a-relative-fd-central-word-face
kind: claim
title: A toric gap is a relative finite-dimensional state-face failure, and phase-safe normal closure centralizes every player word
distinct_from:
  phase-safe-toric-gap-game-exists: that asks for an actual finite gap game; this identifies the exact representation-theoretic face it must separate and the exact structure of its phase-safe quotient
  phase-safe-toric-gap-implies-nonhyperlinear: that is the positive groupification theorem once a phase-safe gap exists; this is a structural audit of the missing game/compiler
  perfect-lcs-gap-implies-nonhyperlinear: an LCS solution group is a structured specialization; the criterion here applies to every two-player torically determined game
---

ESTABLISHED.  There are two exact structural reductions which sharply limit
what can be obtained from residual finite-dimensionality or from a
state-dependent reversible ancilla.

## 1. The clause-character face

Let `G=G_A x G_B` be the universal group of a finite two-player game.  Each
one-player factor is a finite free product of finite cyclic groups.  Let `B`
be the finite scalar phase group and suppose the game is torically determined
by clauses

```text
h_i=(beta_i,g_i) in B x G.
```

Write `H=<h_i>`.  If `H intersect B={1}`, projection to `G` identifies `H`
with the graph of a finite character

```text
chi:K=proj_G(H) -> B.
```

Let `S_fd(G)` be the set of vector states of finite-dimensional unitary
representations of `G`, and let its closure be weak star closure in the state
space of `C*(G)`.  Define the clause face

```text
F_(K,chi)={phi: phi(chi(k) k)=1 for every k in K}.
```

It is enough to impose this on the finite clause generating set.  Since the
clauses are unitaries, equality of the state value to one is equivalent in the
GNS representation to the cyclic vector being fixed by every clause.

> **Theorem 1 (relative-FD face criterion).**  For a finite torically
> determined game,
>
> ```text
> omega_qa=1
>   iff
> F_(K,chi) intersects closure(S_fd(G)).                 (RTF1)
> ```

### Proof

If finite-dimensional strategies have values tending to one, take their
vector states on `C*(G)`.  A weak-star cluster point exists.  Every losing
projection has expectation zero in the limit, so the limiting strategy is
perfect.  Because the game is determined by the toric clauses, its GNS vector
is fixed by every clause.  The limit state therefore lies in the displayed
intersection.

Conversely, let a state in the clause face be a weak-star limit of
finite-dimensional vector states.  Its GNS vector is fixed by every clause,
so the determining property makes it a perfect strategy.  There are only
finitely many losing projection products, and each is a finite linear
combination of elements of `G`.  Weak-star approximation on those finitely
many coefficients gives finite-dimensional strategies whose losses tend to
zero.  Hence `omega_qa=1`.  End proof.

Thus a toric `qc=1>qa` gap is not merely failure of residual finiteness of a
group.  It is failure of finite-dimensional state approximation on one
specific face cut out by a finitely generated infinite-index subgroup and a
finite character.

There is a canonical monomial perfect representation

```text
Ind_K^G(conjugate(chi)),                                (RTF2)
```

with its distinguished coset vector.  Approximation of that vector state by
finite-dimensional states is sufficient to force `omega_qa=1`.  Failure to
approximate only that one state is not sufficient for a gap: `(RTF1)` says
that **every** state in the clause face must be excluded.

## 2. What RFD does and does not imply

> **Corollary 2.**  If `C*(G)` is residually finite dimensional, no finite
> game with universal group `G` can have `omega_qc=1>omega_qa`.

Indeed, finite-dimensional vector states are then weak-star dense in the
whole state space.  One proof is to take the direct sum of a separating
family of finite-dimensional representations.  It is faithful.  Convex
combinations of its vector states are weak-star dense by separation of
selfadjoint elements, and every finite convex combination is one vector state
in a finite direct sum of finite-dimensional representations.  Apply
Theorem 1 to a perfect state.

By itself this does **not** give a no-go for arbitrary toric clause faces.  The one-player
groups `G_A,G_B` are virtually free and their full group C-star algebras are
RFD, but

```text
C*(G_A x G_B)=C*(G_A) tensor_max C*(G_B).              (RTF3)
```

RFD does not pass to this maximal tensor product.  When both factors contain
nonabelian free groups, the product contains `F_2 x F_2`; after the negative
solution of Connes embedding, `C*(F_2 x F_2)` is not RFD.  Kirchberg's
equivalence between Connes embedding and RFD of `C*(F_2 x F_2)` is recorded,
for example, in Pestov--Uspenskij, arXiv:math/0601700, Theorem 10.  Hence
separate one-player property FD/RFD cannot approximate a commuting two-player
state.  The maximal-tensor obstruction is exactly where a toric gap could
live without the normal phase-safe hypothesis.

Normal phase safety removes that freedom.  Combining the central-product
formula below with extension of abelian characters produces a perfect
**product** state in the clause face; separate one-player RFD then
approximates that state.  This is
`normal-phase-safe-toric-games-have-qa-one`, and it rules out a strict gap
under `(RTF7)`.

## 3. Exact structure after phase-safe normal closure

Write each clause uniquely as

```text
r_i=(beta_i,a_i,b_i) in B x G_A x G_B.
```

Define the one-player centralization quotients

```text
A_0=G_A / <<[a_i,x]: all i, x in G_A>>,
B_0=G_B / <<[b_i,y]: all i, y in G_B>>.                (RTF4)
```

The displayed normal closures are finitely normally generated: it is enough
to take `x,y` from fixed finite generating sets.  Let `abar_i,bbar_i` be the
images of the clause words.  They are central in `A_0,B_0`.  Put

```text
Z=< (beta_i,abar_i,bbar_i): all i >
  <= B x Z(A_0) x Z(B_0).                              (RTF5)
```

> **Theorem 3 (normal toric quotient formula).**  If `N` is the normal
> closure of the clauses in `B x G_A x G_B`, then
>
> ```text
> (B x G_A x G_B)/N
>   ~= (B x A_0 x B_0)/Z.                              (RTF6)
> ```
>
> In particular, phase safety is exactly
>
> ```text
> Z intersect B={1}.                                   (RTF7)
> ```

### Proof

In the quotient by `N`, the equation

```text
beta_i a_i b_i=1
```

makes `a_i b_i` central.  Since the two player subgroups commute, for every
`x in G_A` and `y in G_B`,

```text
[a_i b_i,x]=[a_i,x],
[a_i b_i,y]=[b_i,y].                                  (RTF8)
```

Thus `N` contains all relations in `(RTF4)`, and the quotient factors through
`B x A_0 x B_0`.  There every remaining clause `(beta_i,abar_i,bbar_i)` is
central, so its normal closure is just the central subgroup `Z` it generates.
The two quotient presentations have the same universal property, proving
`(RTF6)`.  Intersecting the kernel with the original central copy of `B`
gives `(RTF7)`.  End proof.

There is a useful scalar-only reformulation of `(RTF7)`.  Let `E` be the
free abelian group on the clause indices and define

```text
alpha:E -> Z(A_0) x Z(B_0),
alpha(n)=prod_i (abar_i,bbar_i)^(n_i),

beta:E -> B,
beta(n)=prod_i beta_i^(n_i).                            (RTF9)
```

> **Corollary 4 (phase-label factorization).**  The normal closure is
> phase-safe if and only if
>
> ```text
> ker(alpha) <= ker(beta),                              (RTF10)
> ```
>
> equivalently, the prescribed scalar label `beta` factors to a character
> on the central subgroup `im(alpha)`.

Indeed, an element of `Z intersect B` is exactly
`(beta(n),1,1)` for some `n in ker(alpha)`.  This criterion separates the two
remaining tasks cleanly: finite-dimensional soundness concerns the state
face `(RTF1)`, while normal phase survival is the consistency of one scalar
character on the central word-pair subgroup.

This does not prove that the quotient is hyperlinear: RFD and hyperlinearity
do not pass to arbitrary quotients, and proving otherwise here would solve
the target problem.  It does show that normal phase safety converts every
cross-player clause into **central one-player word data**.  Noncentral
reversible-circuit semantics cannot simply be carried unchanged through
normal groupification.

## 4. Audit of state-dependent reversible ancillas

A reversible finite packet can compute an arbitrary Boolean truth table on a
chosen representation type.  This does not yet give a toric compiler.

1. A one-round player cannot locally compute the reflection of a joint losing
   projection `P_a^x P_b^y`: its two factors belong to different players.
   A sequential controlled operation would require communication or extra
   consistency tests.
2. On one local finite packet, selecting the intended computational type is
   not automatic.  Inducing a character of the selector subgroup into the
   finite packet recreates every compatible selector character, including the
   forbidden ones.  Thus ordinary finite packet relations do not make the
   controlled reflection universal.
3. If additional toric clauses do make the construction phase-safe, Theorem
   3 says that their normal quotient retains only centralizations of the two
   player word components and central identifications between them.  Robust
   soundness must therefore be proved on the relative state face `(RTF1)`, not
   inferred from the intended reversible circuit representation.

The reversible/ancilla route to a finite normal phase-safe toric gap is
consequently disproved.  The stronger direct quotient target remains:

> Find a normal finite-phase projective-kernel face disjoint from all CE
> **tracial** states and quotient directly, without asking those relators to
> determine a finite two-player game.  This is
> `monomial-finite-phase-ce-kernel-face-gap`.

That is a state-dependent, central-word version of the perfect-LCS/projective-
kernel compiler.  Separate property FD, ambient residual finiteness, a local
finite reversible packet, or approximation of one induced vector state does
not supply it.

## Primary sources

- Watts--Helton--Klep, *Noncommutative Nullstellensaetze and Perfect Games*,
  arXiv:2111.14928, especially the definition of torically determined games
  and Theorem 5.12.
- Pestov--Uspenskij, *Representations of residually finite groups by
  isometries of the Urysohn space*, arXiv:math/0601700, Theorem 10.
- Ji--Natarajan--Vidick--Wright--Yuen, *MIP*=RE*, arXiv:2001.04383, for the
  negative solution of Connes embedding used in the RFD audit.
