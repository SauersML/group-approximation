---
rg: 2
id: block-diagonal-pair-grams-do-not-add-coverage
kind: claim
title: A block diagonal sum of pairwise Gram states averages their game coverage instead of gluing it
distinct_from:
  pairwise-cross-grams-do-not-supply-one-game-state: that gives the direct-sum edge-space countermodel to a common Gram state; this audits the proposed repair of using the direct sum itself as the strategy state and computes its exact game value.
  one-gram-vector-decodes-a-finite-bcs-strategy: that turns one Gram operator with low full game energy into a strategy; this proves that putting several partial Gram operators on orthogonal blocks does not make any one block carry the missing questions.
  fanizza-product-gram-reduces-to-one-state-holonomy: that coherently transports all contexts into one rooted Gram state; this deliberately avoids that chain/holonomy construction and tests only the incoherent direct-sum bypass.
---

## Verdict

The direct-sum construction is a valid finite-dimensional strategy, but it
does not add the question sets certified by its blocks.  It takes a convex
mixture of the pair strategies.  The hidden block label is selected before
the verifier's questions, so the certified coverage is the **average** block
coverage, at most the coverage of the best single block.

For the `k`-context pair-carrier model this remains `2/k`, not `1`; for the
actual Fanizza incidence it is generally smaller because an oriented
cross-Gram block certifies only the shared-variable rounds, not every round
at its two endpoint contexts.  Consequently choosing a game with
`omega^*<=theta` gives a contradiction only if one already knows that one
pair block covers question mass greater than `theta`.  The direct sum creates
no such inequality.

Lin's arbitrary Bell-separation parameter does not close the numerical loop.
For separation `delta`, the finite-dimensional soundness is
`theta=1-delta`.  Although any fixed `theta>0` may be requested, the resulting
game and its question distribution change with `theta`; the theorem gives no
lower bound on pair coverage relative to `theta`.  A fixed-incidence
soundness amplifier or one full-game Gram state is still required.

## Attempts

- **Put all forced `G_(cd)` on diagonal blocks and claim the union of their
  good contexts.**  The exact mixture formula `(BDG4)` shows that only a
  convex average of the good-context masses is obtained.
- **Include both orientations.**  `G_(dc)=G_(cd)^*` can be placed on another
  block, but it is another classical mixture component and does not make one
  state good in both orientations.
- **Choose Lin's soundness after seeing the coverage.**  Re-running the
  arbitrary-gap compiler changes the number of questions and their marginal
  weights.  No theorem gives a crossing `theta<q(theta)`.

## 1. Exact block-diagonal mixture formula

Let `Game` be a finite two-player game with question distribution `mu`.  Let
`j` range over a finite family of Gram blocks.  Suppose `G_j` and blockwise
measurements decode a finite-dimensional strategy `S_j`.  After a harmless
common amplification, form

```text
G=directSum_j t_j G_j,                                  (BDG1)
```

and use the direct sums of the measurements.  Under normalized
vectorization, the state `vec(G)/||G||_2` is the orthogonal classical mixture
of the states `vec(G_j)/||G_j||_2` with weights

```text
lambda_j
 =t_j^2||G_j||_2^2 / sum_l t_l^2||G_l||_2^2.           (BDG2)
```

Therefore

```text
value(S_G)=sum_j lambda_j value(S_j),                  (BDG3)
```

exactly.  If block `j` is known to win, up to error `epsilon_j`, only on a
set `C_j` of verifier question pairs, then the only unconditional lower bound
is

```text
value(S_G)
 >=sum_j lambda_j[mu(C_j)-epsilon_j]
 <=max_j mu(C_j)+small error.                          (BDG4)
```

The rightmost inequality is the key point.  It is not legitimate to replace
the weighted average by

```text
mu(union_j C_j).                                       (BDG5)
```

The strategy does not learn `j` from the verifier's questions.  Its central
direct-sum label is shared randomness chosen independently of them.

Rescaling the blocks changes the `lambda_j`, but optimizing `(BDG4)` merely
selects the best one.  Thus the direct sum never beats the best pairwise Gram
state already present.

## 2. The PGS model remains at its original coverage

In the model of `pairwise-cross-grams-do-not-supply-one-game-state`, the
blocks are indexed by unordered pairs `{c,d}` of `k` contexts.  If the game
has uniform context marginal and block `{c,d}` is optimistically assumed to
be perfect on **all** rounds whose context lies in `{c,d}`, then

```text
mu(C_(cd))=2/k.                                        (BDG6)
```

Every convex combination in `(BDG4)` has the same coverage `2/k`.  For the
native four-context incidence the direct sum therefore remains at `1/2`,
exactly as the canonical density computation `(PGS5)` already indicated.
Putting all six pair blocks on the diagonal does not produce coverage one.

For nonuniform context marginal `nu`, the optimal direct-sum coverage is

```text
max_(c!=d)[nu(c)+nu(d)],                               (BDG7)
```

again the best single pair.

## 3. Left/right orientation makes the actual coverage smaller

The estimate `(BDG6)` is deliberately generous.  A cross-Gram operator has
an orientation.  Schematically, an exact block `G_(cd)` gives rows of the
form

```text
A_(c,x)G_(cd)=G_(cd)A_(d,x)                            (BDG8)
```

for observables `x` actually shared by contexts `c` and `d`.  Under
vectorization this supplies Alice's `c` occurrence on the left and Bob's
`d` occurrence on the right.  It does not imply

```text
[A_(c,y),G_(cd)]=0                                     (BDG9)
```

for a private variable `y` of context `c`, nor does it provide all other Bob
questions in that context.

The adjoint `G_(dc)=G_(cd)^*` handles the reverse orientation, but placing it
on a second block only adds a second term to the mixture `(BDG3)`.  Hence the
honest certified set `C_(cd)` for the current pairwise bridges consists of
the shared-variable incidences for which `(BDG8)` is available, not both full
endpoint stars.  Its `mu`-mass can be much less than `2/k`.

Local predicate satisfaction does not repair `(BDG9)`.  It makes Alice's
answer legal in the owning context on the relevant state, but consistency
with one common Bob family is a separate left/right equation.  This is why
`one-gram-vector-decodes-a-finite-bcs-strategy` asks for every row

```text
A_(c,x)G=GB_x                                          (BDG10)
```

on the same `G`.

## 4. Shared-variable consistency does not glue across blocks

There is no obstruction to defining

```text
B_x=directSum_j B_x^(j).                               (BDG11)
```

Thus different pair blocks may use completely different Bob realizations of
the same logical variable.  Equation `(BDG11)` is a legal measurement in the
direct-sum strategy.  This explains both sides of the result:

- cross-block inconsistency does not cost the strategy anything;
- but consistency proved in block `j` gives no information in block `l`.

State-dependent triangle inequalities cannot cross the central block
decomposition.  Direct sum therefore preserves precisely the PGS escape
rather than eliminating it.

## 5. Exact threshold criterion

Let `q_j=mu(C_j)` and suppose the uncovered rounds are assigned arbitrary
valid measurements.  Since a loss probability is at most one, a block with
error `epsilon_j` on `C_j` gives

```text
value(S_j)>=q_j-epsilon_j.                             (BDG12)

```

If `omega^*(Game)<=theta`, every block consequently satisfies

```text
q_j<=theta+epsilon_j.                                  (BDG13)

```

and `(BDG3)` gives only the averaged version of the same inequality.  Thus a
pair-block group compiler would indeed obtain a fixed energy floor if it
forced some

```text
q_j>theta.                                             (BDG14)

```

But `(BDG14)` makes the direct sum unnecessary: that single block already
decodes a strategy whose value exceeds the finite-dimensional game value.
The entire proposed bypass has therefore reduced to a source theorem saying
that one forced partial strategy covers more question mass than the game's
soundness.

This observation is also a useful sanity check.  Whenever a genuine finite
partial strategy wins all rounds in `C_j`, extending its measurements
arbitrarily outside `C_j` proves

```text
omega^*(Game)>=mu(C_j).                                (BDG15)

```

So a low-soundness game must prevent high-mass locally realizable patches or
spread its distribution enough that every such patch has small mass.

## 6. What Lin's arbitrary parameter does and does not say

Lin's Theorem 6.15 is stated for the `delta`-Bell separation promise

```text
|omega^*(Game)-omega^co(Game)|>=delta.                 (BDG16)

```

On the perfect commuting side `omega^co=1`, so `(BDG16)` gives

```text
omega^*(Game)<=1-delta.                                (BDG17)

```

The remark following the theorem says that the proof can use any fixed
`delta in (0,1)`.  Equivalently one may request any fixed positive soundness
target `theta=1-delta`.

What is **not** asserted is a family `Game_theta` with

```text
theta < max_j mu_theta(C_(theta,j)),                   (BDG18)

```

or even a lower bound on the smallest question/context mass as a function of
`theta`.  The compression, question reduction, verifier, and distribution
all depend on the requested soundness.  If one first computes
`Game_theta`, observes its number of contexts, and reruns the compiler with a
smaller target, the context number and coverage fractions change again.
The arbitrary-constant statement alone gives no crossing of this moving
target.

This is not a cosmetic quantitative omission.  Any standard game whose
predicate has an accepting answer on each sampled question pair satisfies

```text
omega^*(Game)>=max_(x,y)mu(x,y),                       (BDG19)


```

by a strategy tailored to the heaviest pair.  Therefore arbitrarily small
soundness necessarily comes with correspondingly small locally satisfiable
question mass unless additional incompatibility is proved.  The verifier is
allowed to spread its distribution as its gap is amplified.

## 7. Exact claim boundary

This audit does not rule out a source-specific low-soundness game whose
question incidence is fixed and for which the actual forced Gram patch has
mass `q>theta`.  Such a game would close the matrix contradiction
immediately, and only one pair block would be needed.

Current inputs do not supply it.  The PGS pairwise overlaps use different
states; their honest left/right coverage is only the shared incidence.  Lin's
arbitrary separation constant gives no soundness-versus-coverage estimate.
Consequently the live repairs remain:

1. produce one Gram operator carrying the full game energy `(OGV3)`;
2. coherently transport the pair blocks through a chain/holonomy cell; or
3. prove a fixed-incidence gap amplifier whose soundness drops below a
   verified pair-patch mass without shrinking that mass.

The block-diagonal sum alone is not such an amplifier.

