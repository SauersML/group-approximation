# External open-problem reconnaissance — 2026-08-18

This is deliberately **noncanonical Cairn state**.  The pass was useful as a
research-method audit and as negative knowledge, but it produced no theorem that
has an honest implication into the current group-approximation roots.  Keeping it
in `notes/` makes it searchable without manufacturing unrelated graph nodes.

## Scope

The goal was to look well outside the repository's usual operator-algebra/group-
approximation neighborhood for old, named open problems with small exact
certificates, then attack one hard enough that either a construction or a complete
finite obstruction could in principle be independently checked.

Repository searches on 2026-08-18 found no relevant Cairn/Lean material for
`Leech tree`, `perfect distance`, `Hadamard 668`, or `Littlewood Richardson hive`.
That absence is not itself mathematics; it only establishes that these were not
already hidden under the obvious vocabulary in this repository.

## Order-18 Leech trees / perfect distance trees

### Problem and status checked

A Leech (perfect-distance) tree on `n` vertices is a positively integer-weighted
tree whose `n choose 2` pairwise path weights are exactly

```text
1, 2, ..., n choose 2.
```

For `n = 18` the target distance set is `1..153`.  The 2007 paper *Minimal
Distinct Distance Trees* determines all perfect distance trees for `n < 18`, so
18 is the first order not covered by that classification.  A targeted current
search on 2026-08-18 found no later resolution; the 2024 paper *A graph labeling
problem* still studies structural restrictions on Leech trees rather than giving
an order-18 construction/classification.

Sources checked:

- Calhoun et al., *Minimal Distinct Distance Trees*, JCMCC 61 (2007):
  <https://combinatorialpress.com/jcmcc-articles/volume-061/minimal-distinct-distance-trees/>
- Tao Luo and Leah Yu, *A graph labeling problem*, Involve 17 (2024), 327–335,
  DOI 10.2140/involve.2024.17.327:
  <https://msp.org/involve/2024/17-2/involve-v17-n2-p09-s.pdf>
- Current secondary status cross-check (MathWorld, checked 2026-08-18):
  <https://mathworld.wolfram.com/TaylorsCondition.html>

### Exact reductions independently rederived

For an order-18 solution, Taylor parity specializes to a forced vertex parity
split of `7 + 11`: there are 77 odd target distances among `1..153`, and if the
two parity classes have sizes `a,b` then `a+b=18` and `ab=77`.

The first distance moment gives the exact cut equation

```text
sum_e w_e * s_e * (18 - s_e) = 1 + ... + 153 = 11781,
```

where deleting edge `e` leaves sides of sizes `s_e` and `18-s_e`.  The square
moment target is

```text
sum_{x<y} d(x,y)^2 = 1^2 + ... + 153^2 = 1205589.
```

These are valid necessary conditions, but the safe partial-state relaxations of
the cut sizes were too weak to close the order-18 search.

### Forced-next-edge recursion — useful, but prior art

A clean recursion was independently rederived:

> Given the forest formed by the currently exposed smallest edge weights, let
> `m` be the smallest positive integer not represented by a path inside the
> forest.  In any completion to a Leech tree, the next-smallest edge weight must
> be exactly `m`.

Proof: if the next unused edge weight is `w`, then `w` is itself a new endpoint
distance, hence `m <= w`.  If `m < w`, any completed path of weight `m` cannot use
an unexposed edge (all are at least `w` and weights are positive), so it was
already represented in the current forest, contradicting the definition of `m`.
Thus `w=m`.

This initially looked like the key new idea.  The prior-art audit killed the
novelty claim.  Yong Zhang's preserved 2004 program for the Székely–Wang–Zhang
9-node search has a `nextvalue_matrix` routine explicitly described as returning
“the smallest integer that can not be represented by the given graph,” and uses
that return value as the next edge label.  The relevant routine is around lines
591–629 of the public source:

- program index: <https://people.math.sc.edu/laszlo/leechtree/index.htm>
- 9-node source: <https://people.math.sc.edu/laszlo/leechtree/ninenode.c>

So this is a rediscovery of an existing computational reduction, not a new Leech
lemma to claim.

### Search actually completed

The recursion was rebuilt using canonicalized weighted forest components and a
Taylor-parity feasibility check.  It was validated by reconstructing a known
6-vertex Leech tree before being applied at order 18.

The complete canonical prefix enumeration reached depth 9 (nine assigned edges):

| assigned edges | canonical valid states |
|---:|---:|
| 0 | 1 |
| 1 | 1 |
| 2 | 2 |
| 3 | 8 |
| 4 | 41 |
| 5 | 229 |
| 6 | 1,384 |
| 7 | 8,899 |
| 8 | 62,843 |
| 9 | 480,085 |

Several tiny high-next-weight depth-9 buckets were then exhausted, and deeper
branches were explored with moment pruning.  No order-18 tree was found.  **The
low-next-weight continuation space was not exhausted.**  Therefore this is neither
a construction nor a nonexistence proof, and no Cairn claim/route is justified.

The important reusable distinction is:

```text
complete recursion theorem + partial traversal != exhaustive nonexistence proof.
```

A negative theorem would require a replayable exhaustion of every remaining
canonical state in addition to proofs that canonicalization and every pruning rule
preserve completeness.

## Hadamard order 668 — correction to the reconnaissance

An intermediate status update in this research pass incorrectly stated that the
order-668 Hadamard problem had been solved on 2026-08-13.  That statement was
wrong and must not be propagated.

A fresh check on 2026-08-18 finds order 668 **still unresolved**:

- Epoch's current FrontierMath problem page labels “Find a Hadamard matrix of
  order 668” **Unsolved** and calls 668 the smallest order for which no matrix is
  known:
  <https://epoch.ai/frontiermath/open-problems/hadamard>
- Ramos–Hulak–de Queiroz, arXiv:2607.20765 (submitted 2026-07-22), explicitly
  calls 668 the smallest order presently unresolved; it proves obstructions only
  for common-multiplier Legendre-pair subfamilies and states that unrestricted
  existence remains open:
  <https://arxiv.org/abs/2607.20765>

This correction is the strongest process lesson from the pass: benchmark status is
itself a freshness-sensitive claim.  A single search snippet or unverified report
is not enough to promote “solved” or “open” into durable research state.

No Hadamard node was added to Cairn because it is off-axis from the current roots,
and this pass did not produce a matrix or a new theorem about order 668.

## Stretched Littlewood–Richardson / KTT positivity attack

A second exploratory lane built an exact integer hive enumerator for
Littlewood–Richardson coefficients and used exact interpolation on stretches.
Representative computations produced positive stretch polynomials; thousands of
targeted exact candidates were searched without finding a negative coefficient.

That is only a failed computational search.  It gives no counterexample and no
proof of positivity, and the representation-theoretic lane is less cleanly
separated from material already adjacent to this repository.  Nothing from it is
promoted to canonical Cairn state.

## What is worth carrying forward

1. **External freshness is a proof obligation for status claims.** Recheck named
   open problems on the date of attack.
2. **Search code as prior art.** The Leech recursion was present in released C
   source even though independently deriving it felt novel.
3. **Separate certificate classes.** A positive finite object needs an exact
   verifier; a finite nonexistence theorem needs a complete recursion plus a full
   replayable exhaustion; a partial search is only scoped evidence.
4. **Record exact scope of computation.** “No solution found” is meaningless
   without saying which state space was exhausted.
5. **Do not pollute Cairn with off-axis mathematics.** Interesting external work
   belongs in searchable notes unless it yields an honest reusable implication
   into the program.

These rules are now summarized in `research/README.md` under **External
reconnaissance and computational claims**.  No `research/*.md` claim or route and
no Lean theorem is added by this pass.
