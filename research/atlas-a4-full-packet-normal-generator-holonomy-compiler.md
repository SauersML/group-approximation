---
rg: 2
id: atlas-a4-full-packet-normal-generator-holonomy-compiler
kind: claim
title: The full A4 packet compiles multiplicity holonomy to an A8 representation on which collision 19243 reads the normal generator
distinct_from:
  atlas-a4-rank-three-core-commutant-collapse: the fourteen-word route stops inside H=GL3(2); this compiler deliberately retains the central C3 packet directions so the residual holonomy closes to the full simple chart group A8.
  atlas-a4-componentwise-commutant-collapse: that asks directly for closeness to two subgroup commutants; this target asks for a representation-valued compiler certificate from which commutant collapse follows by normal-generator stability.
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
  - experiments/atlas_a4_19243_normal_closure.py
---

Let `sigma_n` be an exact-regular normalized thirty-context A4 network as in
`atlas-a4-holonomy-coherence-gap`, let `U_n` be its relative `A8` chart frame,
and put

```text
eta_n = max ||sigma_n(t)-1||_2
```

over the fixed non-tree stable letters.  Thus `eta_n->0`.

Using the canonical qutrit/multiplicity splitting of every regular A4 context,
compile the finite packet coherence data into exact finite-dimensional unitary
representations

```text
pi_n : A8 -> U(M_n)
```

and their invariant projections `Q_n` so that there are constants
`C_frame,C_col<infinity`, independent of `n` and of the external multiplicity,
with

```text
dist_2(U_n, lambda_(k_n)(A8)')^2
 <= C_frame ( tr_(M_n)(1-Q_n) + eta_n^2 ),             (A4-NG-COMP-1)

||pi_n(b)-1||_2
 <= C_col ( ||sigma_n(q_19243)-1||_2 + eta_n ).        (A4-NG-COMP-2)
```

Here `b` is the repeated first-chart involution in `q_19243`.  The spaces
`M_n` may be chosen as fixed finite direct sums of the canonical multiplicity
wires, so their normalized traces remain commensurable with the original
normalized Hilbert--Schmidt trace by constants depending only on the fixed
thirty-context compiler.

The point of the target is **not** to round the relative frame to a classical
chart automorphism.  It asks only for a finite-state holonomy representation:
the packet rectangles supply the transition generators, the central `C3`
directions force the transition group to leave the affine parabolic and close
to `A8`, and collision `19243` reads one normal generator of that finite group.
Once this interface is proved, `atlas-a8-19243-normal-generator-hs-stability`
annihilates every nontrivial multiplicity sector automatically.

## Attempts

- **Gauge the two bicliques first.**  Apply
  `unitary-k2m-rectangle-synchronization` to `K_(2,2) disjoint_union K_(2,4)`.
  Only four matrix holonomies remain.  Interpret their action on the canonical
  qutrit multiplicity wires as a finite groupoid cocycle rather than as thirty
  unrelated gauges.
- **Use the central C3 as a type-checking instruction.**  The exact subgroup
  ladder says the fourteen-word core and `q_19243` never leave
  `P=AGL_3(2)`, where `b` kills only the translation radical.  The discarded
  `C3` labels are exactly the transitions taking `P` to `A8`.  Require those
  edges to implement the conjugacy rules of the full chart group before
  reading the collision.
- **Finite-group cocycle rounding.**  After the graph gauge, all multiplication
  tables are fixed finite data.  Average an approximate multiplicity cocycle
  over the finite groupoid, or equivalently solve the finite intertwiner
  equations and use amplification-stable subspace angles, to obtain exact
  `pi_n` without a dimension-dependent constant.
- **Prove the two inequalities separately.**  `(A4-NG-COMP-1)` is a decoder:
  nontrivial holonomy mass is the only obstruction to placing the relative
  chart frame in the right-regular commutant.  `(A4-NG-COMP-2)` is a verifier:
  telescoping the fixed eight-syllable collision through the compiled gauges
  measures precisely the translation generator `b` up to stable-letter error.
