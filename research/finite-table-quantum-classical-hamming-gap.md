---
rg: 2
id: finite-table-quantum-classical-hamming-gap
kind: claim
title: Some finite table is solvable to arbitrary unitary accuracy but not by permutations
distinct_from:
  hyperlinear-nonsofic-group: that is the existence of a hyperlinear group that is not sofic; this is a finite, table-level statement with no group in it — it is what nonsoficity of such a group would look like locally, and on its own it produces no group at all.
  coherent-groupification-of-table-gap: that is the second half of the separation — embedding such a table coherently into one hyperlinear group; this is the first half, the existence of the gap itself, and is a purely finite question.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target (first half of Target C of the source dossier).**  There is a finite
partial multiplication table `T` and a constant `c > 0` such that

```text
inf { multiplicative defect of a unitary model of T }      = 0,
inf { Hamming defect of a permutation model of T }         ≥ c,
```

the first infimum taken over all matrix dimensions.  Equivalently: an exposed
linear functional separates the quantum and classical feasible regions of the
group-table face of `group-table-cpsd-cp-face-collapse`, robustly.

**Why the finite form is the right first target.**  If some hyperlinear group
is not sofic then such a table and such a `c` exist, by definition — nonsoficity
is a statement about one finite window, and hyperlinearity supplies unitary
models of every accuracy for it.  So the separation answer to Q3.4 *implies*
this claim, and the claim is a strictly finite object that can be searched for
computationally rather than constructed by rigidity.  It is the negative
counterpart to the observation that the affirmative answer only needs
table-dependent rounding.

**What it does not give.**  A gap alone is not a group: see
`coherent-groupification-of-table-gap`.  Finite-dimensional quantum advantage
is common — nonlocal games with perfect quantum and imperfect classical value
are standard — and the gadgets realizing it typically generate linear groups,
which are sofic.  So this claim is necessary and far from sufficient, and its
value is that it is falsifiable on small instances: a systematic absence of
robust gaps across group tables would be real evidence for
`group-table-cpsd-cp-face-collapse` and hence for the affirmative answer.

## Attempts

- **Reuse a known nonlocal-game gap.**  Dies at the groupification step, not
  here, but it also dies here in the following sense: the gaps in the
  literature are for constraint systems with free variables, whereas the
  variables of a group table are invertible, associatively composed and
  uniformly distributed at the regular trace.  No published gap instance is
  known to survive those four constraints, and the standard ones (magic
  square, linear system games) have classical solutions once the variables are
  required to be a group table's regular representation.
- **Take `T` to be the multiplication table of a known nonsofic group.**
  Circular in the wrong direction: the Kun–Thom groups are nonsofic but nothing
  says their tables have unitary models of every accuracy — that is precisely
  the hyperlinearity question those candidates leave open.  Recorded because it
  is the first thing one tries.
- **Search small tables numerically.**  Deferred, and the recommended route:
  optimize the quantum side by a noncommutative moment/SOS hierarchy and the
  classical side by integer programming over permutations, on tables with a
  genuine associativity square.  The obstacle is that a numerical gap at a
  fixed relaxation level is not a gap — the quantum infimum is over all
  dimensions, so only a converging hierarchy or an explicit sequence of
  unitary models certifies the first line.
