---
rg: 2
id: qutrit-jacobson-central-line-twist-is-similarity-impossible
kind: claim
title: No Jacobson matrix can twist the central qutrit line into a leaf line
artifacts:
  - research/qutrit-jacobson-cycle-rank-obstruction-proof.md
distinct_from:
  qutrit-two-to-one-phase-graph-requires-central-line-twist: that gives the abstract character-intersection criterion and checks the first S T k word closure; this excludes the required intersection pattern for every matrix over the Jacobson coefficient algebra.
  qutrit-shortest-tk-word-graphs-are-diagonal-or-complete: that exhausts one finite dihedral word subgroup; this is a full-host similarity obstruction with no word-length bound.
  one-balanced-actor-qutrit-bridge-is-jacobson-core: that identifies the generated host as EL_28(J) and leaves a mixed head occurrence open; this proves that no bare group word anywhere in that whole host has the required qutrit phase graph.
---

Let

```text
A=F_2<S,T | TS=1>,        epsilon:A->F_2,
epsilon(S)=epsilon(T)=1,
```

and let the affine qutrit subgroup `C=<J,Z_1>` act on the twenty-seven
packet coordinates, with one extra fixed coordinate. For every
`g in GL_28(A)`, put

```text
H=C intersect gCg^(-1),        H'=g^(-1)Hg.
```

If `|H|=3`, then `H` is the central line `<J>` if and only if
`H'` is the central line. In particular, the asymmetric intersection

```text
one of H,H' is <J>, and the other is a noncentral line
```

never occurs in `GL_28(A)`.

Indeed, evaluation by `epsilon` preserves invertibility and fixes every
scalar qutrit permutation matrix. The central generator `J` consists of
nine three-cycles on the packet and fixes the extra coordinate, so

```text
rank_(F_2)(J-I)=18.
```

Every noncentral element `J^r Z_1^q` with `q!=0` fixes one complete
`u_1`-slice of nine packet leaves and has six three-cycles on the
remaining leaves. Hence

```text
rank_(F_2)(J^r Z_1^q-I)=12.
```

Conjugating `<J>` to a noncentral line over `A` would, after evaluation,
make these two scalar matrices similar over `F_2`, contradicting rank
invariance.

Combined with the qutrit character-intersection criterion, this proves a
full Jacobson-host no-go: every single-word Hecke phase graph in
`EL_28(A)` is complete, empty, or a partial matching; none sends the two
selected phases of `R=e_0+e_1` only to the complementary phase.

Thus the exact D8 polar cannot be completed by inserting any further bare
`S/T` group word from the generated Jacobson core. A surviving
continuation must either use an element of the full Leavitt host outside
this coefficient subalgebra, where the evaluation obstruction is
unavailable, or obtain branch deletion from a genuinely analytic
raw-residual compression rather than a group-word phase graph.
