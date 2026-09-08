# Torsion-free transfer: one canonical cover, one class obstruction, two duplicates

Date: 2026-09-08.  Source: an external audit supplied by the user, which
states plainly that it does not settle the general transfer question and
instead supplies a cover, an isolated missing implication, and an
unconditional no-go for central covers.  Every argument below was re-derived
before landing.  No code was run and no Lean was built.

## 1. What the audit contributes, and what the archive already had

| Item | Verdict |
|---|---|
| Central extension with torsion-free total group forces every finite subgroup of the base to be abelian; hence `G_0 x S_3` has no torsion-free central cover | NEW here; landed as `torsion-free-central-cover-forces-abelian-finite-subgroups` |
| `F/[R,R]` is a torsion-free cover with free abelian kernel, same rank | NEW here (no "free abelianized" occurrence in the corpus); landed as `free-abelianized-cover-is-torsion-free` |
| The isolated implication `(D)`: `F/[R,R]` MF implies `F/R` MF | NEW as a stated target; landed OPEN as `free-abelianized-cover-reflects-mf` |
| Every late finitely presented approximation of a group with torsion has torsion | NEW here; landed as `torsion-is-a-finite-datum-torsion-freeness-is-not` |
| MF passes from a finite-index subgroup to the ambient group, by induced representations | **ALREADY ESTABLISHED, and formalized**: `mf-is-commensurability-invariant` via `mf-commensurability-from-radical-heredity`, `GroupApproximation/Sofic/InducedCoronaMF.lean`, `isOperatorMF_of_finiteIndex_subgroup`.  The archive's own note says this half is known in the MF literature.  Not re-authored. |
| A torsion element of the finite residual precludes virtual torsion-freeness | **ALREADY ESTABLISHED**: `finite-torsion-carrier-virtual-torsionfree-criterion`, equivalence (1) iff (2).  Not re-authored. |
| A group all of whose homomorphisms to MF groups are trivial has no proper finite-index subgroup | Immediate from that node plus finiteness of finite groups; recorded in the attempts of the open claim rather than as a node. |

The audit's scope statement is accurate and is repeated here: it proves no
transfer, refutes no transfer, and its central-cover result is an obstruction
to one class of procedures.

## 2. Why the recorded "covers do not work" verdict does not decide `(D)`

Both `torsion-free-finitely-presented-non-mf` and
`torsion-free-countable-non-mf` record, as analyzed dead space, that non-MF
does not pass down along surjections: free groups are residually finite,
hence MF, and surject onto every finitely generated group.  That is correct
and it is why `(D)` cannot be free.  It is a statement about arbitrary
covers.  The distinction that matters:

```text
free cover        F     -> F/R      kernel R,        free of infinite rank
abelianized cover F/[R,R] -> F/R    kernel R/[R,R],  free abelian
```

The known quotient-nonclosure witness `mf-quotient-nonclosure` is precisely
the free cover `F_8 -> E`, whose kernel is non-amenable.  No witness with
abelian kernel is recorded anywhere in this archive.  So the general verdict
kills the general principle and leaves the canonical cover open; the two
node texts have been amended to say which.

Radical functoriality does not help either: for a surjection `q : E -> G` one
has `Rad_MF(E) <= q^(-1)(Rad_MF(G))`, vacuous when `Rad_MF(E) = 1`.  And the
amenable-kernel permanence available here points the other way -- Brude--Sasyk
(`amenable-quotient-preserves-metric-approximability`) has the amenable group
as the quotient and concludes soficity or hyperlinearity, not MF, while
`mf-extension-nonclosure` says MF is not closed under extensions at all.

The one structural handle is the Magnus embedding
`F/[R,R] -> Z^n wr (F/R)` (Magnus--Karrass--Solitar, Corollary 4.10.1, the
same citation the archive's Fox--Magnus lane already uses).  It places the
cover inside a wreath product whose top group is `G`, so the ambient group is
non-MF whenever `G` is; what it does not do is locate the lifted mark inside
the embedded copy.  `mf-radical-product-and-restricted-sum-formulas` handles
restricted sums but not the semidirect twist.

## 3. The two proofs, in brief

**Central covers.**  For finite `P <= G`, pull back and average the central
cocycle: `b(p) = |P|^(-1) sum_r c(p,r)` in `A tensor Q` satisfies
`c(p,q) = b(p) + b(q) - b(pq)`, so `a s(p) -> (a + b(p), p)` embeds
`pi^(-1)(P)` in `V x P`.  Its commutator subgroup lands in the finite
`{0} x P` and is torsion-free, hence trivial.  So `pi^(-1)(P)`, and therefore
`P`, is abelian.  Only centrality and torsion-freeness are used.

**The cover is torsion-free.**  `R` is free (Nielsen--Schreier), so `R/[R,R]`
is free abelian.  If `f^n in [R,R]` then the image of `f` in `F/R` has finite
order `m`.  If `m = 1` then `f in R` and torsion-freeness of `R/[R,R]` gives
`f in [R,R]`.  If `m > 1`, the free group `L = <R, f>` surjects onto `Z/mZ`
with `f -> 1`, and freeness lifts that to `l : L -> Z` with `l(f) != 0`; but
`l` kills `[R,R]`, so `0 = l(f^n) = n l(f)`, a contradiction.

## 4. What would change the verdict

A single quotient-nonclosure witness with abelian kernel would refute `(D)`
and close this route; a proof of `(D)` would produce a torsion-free countable
non-MF group from the archive's existing finitely presented witness with no
Property `(T)` input at all, which is the standing ask of
`property-t-free-torsion-free-fp-non-mf-seed` at the countable level.  Either
outcome is worth more than another general-cover argument.
