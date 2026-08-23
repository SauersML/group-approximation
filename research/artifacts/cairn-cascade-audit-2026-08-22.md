---
title: Cairn cascade audit for the non-hyperlinear-group frontier
date: 2026-08-22
---

# Cairn cascade audit

This audit ranks open claims by two different quantities:

1. **forced cascade:** the number of currently open claims that become
   established if the candidate is established, with no further hypotheses;
2. **mathematical compression:** whether the candidate is materially narrower
   than the theorem it would unlock.

The distinction is essential.  A node can have large graph impact because it
has merely renamed an entire missing compiler theorem.

## Exact high-impact nodes

At commit `ab96f34c`, the graph had 3,335 claims, 2,779 established claims,
43 refutations, 3,363 routes, and 249 frontier holes.  The largest forced
cascades among relevant open claims were:

| claim | forced downstream establishments | reaches `non-hyperlinear-group` | audit |
|---|---:|:---:|---|
| `terminal-diagonal-code-error-without-pinching-displacement` | 13 | indirectly | now reduced through the established alignment and quartic algebra to terminal cut-tree Carleson control |
| `parity-charge-or-green-divergence-has-strict-descent` | 12 | indirectly | substantial combinatorial descent theorem |
| `central-adaptive-peeling-or-noncentral-stopping` | 12 | indirectly | substantial stopping-time theorem |
| `hs-schur-packet-gap-amplification` | 11 | yes | not a local Schur estimate; finite local Schur extensions preserve forbidden mass, so the gain must come from the full cross-context perfect-complete tracial PCP seam |
| `iwahori-cubics-suppress-low-bs-orbit-modes` | 9 | yes | exact periodic modes show the extra exponent cannot come from skeleton dynamics; it must come from the involution and two cubic rows |
| `weyl-defect-koopman-spectral-regularity` | 8 | yes | now reduced to the preceding cubic low-mode estimate |
| `adaptive-all-pairs-schur-replica-table-compiler` | 8 | yes | another presentation of the same uniform compiler seam |
| `finite-presentation-must-expose-whole-module-with-uniform-defect` | 7 immediate / 10 transitive | indirectly | broad uniform-exposure theorem rather than a small local lemma |
| `projective-trace-square-transfer-for-sl3-pair` | 6 | yes | exact representation transfer does not suffice; the missing input is arithmetic-specific control of canonical approximate mixed words |
| `edgeful-or3-coefficient-link-compiler` | 5 | yes | finite coefficient-link certificate with three direct closing routes |

The structurally most central node was
`uniform-kazhdan-homogeneous-lcs-face-groups`, with about twenty transitive
descendants, but it causes no immediate forced establishment and is fenced by
several existing no-go results.  It is not presently the best use of effort.

## Best current cascade: terminal PVM alignment

The former alignment bottleneck has split into a solved geometric half and one
remaining analytic half.

The solved half consists of weighted character hashing, commuting correction
for a slowly growing sampled reflection family, coupling of the corrected
joint PVM to the terminal character PVM, and simultaneous polar/Hall carrier
matching.  Common rotations are gauge and do not obstruct the conclusion.

The exact quartic algebra has now been proved.  For terminal selfadjoint
off-diagonals `O_i`, put

```text
A = L^-1 sum_i O_i^2,    D=tau(A),    theta=max_i ||O_i||_op^2.
```

Then

```text
L^-2 sum_(i,j) ||[O_i,O_j]||_2^2
  <= 4 tau(A^2) <= 4 ||A||_op D,
```

and, under `theta=o(1)`, every bounded-width/bounded-occurrence even parity
remainder and the terminal sign cost are `O(theta D)`.  Thus the remaining
gate has sharpened from a vague quartic ledger to

```text
terminal-cut-tree-carleson-controls-aggregate-offdiagonal
```

which must prove either terminal operator-smallness or a row-Carleson
substitute controlling all three quantities

```text
bounded-face even mixed products,
L^-1 sum_i tau(O_i^4),
tau((L^-1 sum_i O_i^2)^2)
```

by `o(1)D`.  Such an estimate would remove the circular `D/lambda_0` term, establish
`terminal-diagonal-code-error-without-pinching-displacement`, and feed the
already established simultaneous-gauge alignment theorem.  This is the
largest current cascade whose unresolved mathematical content appears
strictly smaller than the downstream program.

The desired extra factor must come from a genuine noncommutative
square-function/Carleson estimate on the retained cut tree.  Per-cut HS
smallness is provably insufficient: a direct sum of `N` two-by-two swaps can
be split blockwise and then linewise so that every cut has squared HS size
`1/N` and total Pythagorean cost one, while the terminal off-diagonal still
has operator norm one and `A=I`.  Balanced parity and complete-pair structure
must exclude this recycling geometry.

## Second concrete cascade: affine-Frobenius projection CRT

The shared-involution incidence problem has an exact one-Gram solution.  For
`X=(q_i)` and `Y=(A_iq_i)`, a common symmetry exists exactly when

```text
X*X = Y*Y,    X*Y = Y*X.
```

Writing `D=X-Y`, the algebraic sufficient condition

```text
D D* D = lambda D
```

makes `lambda^-1 D D*` the required algebraic projection.  Hence the active
construction target is the much sharper
`affine-frobenius-tight-defect-column-frame`: manufacture a compatible defect
column that is a scaled partial isometry while retaining strict affine
deficit.  Success would give the positive canonical group-algebra corner and
therefore a direct non-hyperlinearity proof.

## Direct but arithmetic-specific cascade: the SL3 double

`projective-trace-square-transfer-for-sl3-pair` has five direct routes feeding
it and closes the goal.  However exact projective folding cannot prove it:
a sofic calibration group with a finite-dimensionally invisible central word
has zero exact transfer defect while its canonical double still has separating
microstates.  The viable target must use the specific arithmetic pair and
control canonical approximate mixed words, equivalently exclude the relevant
relative-commutant leak.

## Finite Atlas cascade

The Atlas route has been compressed from a 234-row target to a five-row
operator-phase lift.  If the five saturated rows control the nonlinear phase
defect, existing global coercivity and normal-closure telescoping force the two
`S_3` covariance defects below the certified `1/128` floor.  This is a crisp,
finite, direct-to-goal target, but the five-row operator inequality is still
open.

## Underrated narrow hinges

Three smaller graph nodes have unusually favorable ratios of concreteness to
cascade size.

1. `edgeful-or3-coefficient-link-compiler` has a five-claim forced cascade,
   including the goal, through three distinct routes.  The surviving object is
   finite: choose slot frames and packet-term bijections for a fixed
   ten-coordinate or four-cap packet, add private pivots, and survive one
   phase-consistency check.  Existing cap-holonomy firewalls show that the
   certificate is nontrivial, but it is an excellent finite search target.
2. `thompson-v-r5-coherent-carmichael-family` has only a two-claim cascade,
   but those claims are the one-word strict HS ceiling and the goal.  It asks
   for uniformly bounded multi-cell realization of arbitrary Carmichael stars
   from conjugates of the Bleak--Quick generator `b`.  Literal one-cell and
   common-centralizer versions are already refuted.
3. `triangle-relator-extension-admits-local-ucp-sections` also has a two-claim
   cascade directly to the goal.  It asks for local ucp splitting of one
   explicit Kac--Moody triangle relator extension, equivalently a patterned
   Gram completion with difference-class constraints.  This is deep but
   sharply posed and largely independent of the PCP-style routes.

## Deprioritized high-centrality nodes

- `hs-schur-packet-gap-amplification`: local Schur packets extend exactly after
  amplification without reducing forbidden mass.  Any factor-two improvement
  must be supplied by cross-context powering and synchronization, so the node
  is essentially the full perfect-complete tracial quantum-PCP theorem.
- `weyl-defect-koopman-spectral-regularity`: an exact finite cyclic
  `BS(1,4)` packet has arbitrarily slow Koopman modes.  Skeleton/Iwahori
  dynamics, Parseval, lacunarity, and atomlessness alone do not imply the
  required regularity.  The only remaining rescue is a new far-mode estimate
  from the involution and two cubic rows.
- Fano-cap support: it closes the goal, but extremal traces, pairwise pruning,
  radius-two empty-link pruning, contextwise witness selection, and PCPP repair
  are already fenced.  It remains a high-value theorem, not a narrow hinge.

## Work priority

1. Prove or refute terminal cut-tree Carleson control.
2. Search the finite edgeful-OR3 coefficient-link certificate.
3. Construct the affine-Frobenius tight defect frame.
4. Prove the Atlas five-row operator-phase inequality.
5. Test local ucp splitting for the explicit triangle extension.
6. Search for an arithmetic-specific mixed-word inequality for the SL3 pair.
7. Treat HS-Schur, Weyl/Koopman, and Fano-cap as broad programs unless a new
   intermediate lemma materially narrows them.

This ranking should be rerun whenever one of these intermediate claims changes
status; raw descendant count is not a substitute for red-team compression.
