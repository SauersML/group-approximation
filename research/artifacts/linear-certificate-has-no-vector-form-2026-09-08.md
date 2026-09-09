# The linear relator certificate has no vector form

2026-09-08.  Sixth ingestion into the torsion-free-transfer lane.  The
forwarded material is again the full report; measured against the graph, its
two advertised additions are **Theorem L, which is already landed in full**,
and **Proposition V, which is not**.

## Theorem L was already carded, in both halves

| Dossier | Existing node |
| --- | --- |
| `\|\|w(U)-I\|\| <= C max_j \|\|s_j(U)-I\|\|` characterizes the words killed by every corona homomorphism, no perfectness needed, relators usable after changing `C` | `mf-radical-words-have-linear-certificates` |
| `max_i \|\|U_i-I\|\| <= C max_j \|\|r_j(U)-I\|\|` characterizes the strong input, both directions | `full-mf-radical-linear-relator-inequality` |

The existing word node even carries the quantitative conversion the dossier
does not state — a threshold `(R,eta)` yields the same `R` with `C = 6/eta` —
and records that finite sets of radical words admit a common window and
constant.  The amplification `A_M(U) = (+)_(k<=M) U^(tensor k)` with
`M = ceil(pi/(2 delta))`, the estimates `\|\|A_M(W)-I\|\| >= sqrt 2`,
`\|\|A_M(V)-I\|\| <= M\|\|V-I\|\|` and `M delta < 4`, and the unitary-lifting step
via the polar part are all inside those two nodes and their routes.  None of
that is re-landed.

## Proposition V, re-derived

Let `G = F/R` be nontrivial, let `w` have nonidentity image, and let `S` be
**any** finite subset of `R` — in particular any prescribed finite collection
of conjugates of defining relators.  Then there are a finite-dimensional
unitary tuple and a unit vector with

```text
(s(U) - I)xi = 0  for every s in S,     \|\|(w(U) - I)xi\|\| = sqrt 2.
```

Construction, checked here.  Work in `G` itself.  Let `B` be a finite subset
of `G` containing `1` and every intermediate point of the left-multiplication
trajectory of each word of `S u {w}` applied to `1` — reading a word right to
left, the successive images of `1` under its suffixes.  For each free
generator `x`, left multiplication by `q(x)` restricts to a bijection

```text
{ b in B : q(x)b in B }  -->  { b in B : q(x)^-1 b in B },
```
two subsets of `B` of equal size; extend it by any bijection of the
complements to a permutation `sigma_x` of `B`.  Its inverse then agrees with
multiplication by `q(x)^-1` whenever both endpoints lie in `B`.  Let `U_x` be
the permutation matrix on `l^2(B)` and `xi = e_1`.

Every prescribed word now follows its true trajectory on `xi`, because all
intermediate points were put into `B`.  So `s(U)xi = e_(q(s)) = e_1 = xi` for
`s in S`, since `S` lies in `R`; and `w(U)xi = e_(q(w))`, a basis vector
distinct from `e_1`, at distance exactly `sqrt 2`.

**Consequence.**  No finite `S` and constant `C` satisfy

```text
\|\|(w(U)-I)xi\|\| <= C ( sum_(s in S) \|\|(s(U)-I)xi\|\|^2 )^(1/2)
```
for all finite-dimensional unitary tuples and all vectors.  So the operator
inequality of `mf-radical-words-have-linear-certificates` does **not** upgrade
to the positive-operator inequality obtained by squaring it.

**No conflict with the certificate.**  The certificate bounds `w` by the
largest relator error **on the whole space**, and in this construction the
`s(U)` are far from `I` away from `xi`.  What fails is only the vector form.

**The methodological point.**  With `P` the rank-one projection onto `xi`,
`(s(U) - I)P = 0` for every selected relator while `\|\|(w(U) - I)P\|\| = sqrt 2`.
But the compressions `P U_x P` are **not unitary**.  So a common fixed vector
for a finite set of relators cannot be treated as a finite-dimensional
quotient representation, and compression is not a repair for the descent
problem.

## Why the certificate still does not give the transfer

Recorded as an Attempts bullet on `free-abelianized-cover-reflects-mf`.  In
`E = F/[R,R]` the elements represented by the original relators `r_j` lie in
the free abelian kernel and are **not** required to be the identity.  A matrix
model of `E` must make the relevant commutators between their conjugates
small; it need not make `r_j(U) - I` small.  So the right-hand side of the
certificate is not controlled on such models, and applying it to a
prospective separating model of `E` merely forces some kernel relator to stay
quantitatively visible — which is compatible with injectivity of the cover's
corona representation, not a contradiction.

## Scope

Proposition V is a counterexample to a strengthening of an existing estimate,
not to the estimate, and not to `(D)`.  No Lean certification is asserted.
