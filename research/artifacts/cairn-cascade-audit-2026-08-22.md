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

At the audited graph state, the largest forced cascades among relevant open
claims were:

| claim | forced downstream establishments | reaches `non-hyperlinear-group` | audit |
|---|---:|:---:|---|
| `multicharacter-pvm-alignment-modulo-simultaneous-gauge` | 13 | indirectly | genuinely narrow; its alignment part is now established and the remaining prerequisite is the terminal quartic ledger |
| `parity-charge-or-green-divergence-has-strict-descent` | 12 | indirectly | substantial combinatorial descent theorem |
| `central-adaptive-peeling-or-noncentral-stopping` | 12 | indirectly | substantial stopping-time theorem |
| `hs-schur-packet-gap-amplification` | 11 | yes | not a local Schur estimate; finite local Schur extensions preserve forbidden mass, so the gain must come from the full cross-context perfect-complete tracial PCP seam |
| `weyl-defect-koopman-spectral-regularity` | 8 | yes | skeleton dynamics alone is false; only uniform suppression of far/outlier modes by the involution and two cubic rows can rescue it |
| `adaptive-all-pairs-schur-replica-table-compiler` | 8 | yes | another presentation of the same uniform compiler seam |
| `finite-presentation-must-expose-whole-module-with-uniform-defect` | 7 immediate / 10 transitive | indirectly | broad uniform-exposure theorem rather than a small local lemma |
| `projective-trace-square-transfer-for-sl3-pair` | 6 | yes | exact representation transfer does not suffice; the missing input is arithmetic-specific control of canonical approximate mixed words |

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

The remaining gate is

```text
aggregate-terminal-even-defect-is-quartic-summable
```

in the form

```text
E_bal(sign(Phi_F(Q))) <= C (epsilon + rho D),
```

or any estimate with `o(1) D`, where `D` is the exact Pythagorean terminal
cut displacement and `rho -> 0` bounds the individual retained cut scale.
Such an estimate would remove the circular `D/lambda_0` term, establish
`terminal-diagonal-code-error-without-pinching-displacement`, and feed the
already established simultaneous-gauge alignment theorem.  This is the
largest current cascade whose unresolved mathematical content appears
strictly smaller than the downstream program.

The promising proof shape is a lowest-common-ancestor decomposition of
terminal off-diagonal blocks.  Exact Pythagoras supplies orthogonality; exact
even-parity expansions ensure every new error term contains at least two
off-diagonal factors.  The desired extra factor `rho` must come from a
noncommutative square-function/Carleson estimate on the retained cut tree.

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

1. Prove or refute the quartic terminal cut-tree estimate.
2. Construct the affine-Frobenius tight defect frame.
3. Prove the Atlas five-row operator-phase inequality.
4. Search for an arithmetic-specific mixed-word inequality for the SL3 pair.
5. Treat HS-Schur, Weyl/Koopman, and Fano-cap as broad programs unless a new
   intermediate lemma materially narrows them.

This ranking should be rerun whenever one of these intermediate claims changes
status; raw descendant count is not a substitute for red-team compression.
