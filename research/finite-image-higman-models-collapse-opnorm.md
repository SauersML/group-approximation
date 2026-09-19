---
rg: 2
id: finite-image-higman-models-collapse-opnorm
kind: claim
title: Operator-norm approximate Higman tuples generating a finite group collapse linearly
artifacts:
  - research/finite-image-higman-models-collapse-opnorm-proof.md
  - experiments/finite-image-collapse-2026-09-17/check_finite_image_collapse.py
distinct_from:
  one-small-higman-generator-collapses-the-four-cycle: that assumes one generator is spectrally small and allows arbitrary (infinite) generated groups; this assumes nothing about any generator's spectrum and instead assumes the generated subgroup of U(k) is finite, with constant 1 and threshold 1/2.
  higman-four-cycle-intrinsic-mf-seed: that is the open dimension-uniform collapse for all approximate Higman tuples; this proves it, with an explicit linear constant, on the class of tuples whose generated group is finite, and shows every countermodel must generate an infinite subgroup.
  higman-exact-packet-cycles-collapse-opnorm: that is the open (CGC); this proves (CGC) with epsilon=3 eta for every exact packet cycle whose conjugators generate a finite group, and kills all finite-group countermodel ansaetze.
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that builds root-of-unity clocks with three small seams; this shows that no completion of such a clock inside a finite subgroup of U(k) can make the fourth seam small.
---

**ESTABLISHED.**  Let `G = <X | R>` be a finitely presented group with no
nontrivial finite quotient.  Write `E` for its `R x X` exponent-sum matrix.
Because `G` has no finite quotient, `H_1(G) = Z^X / Z^R E` is a finitely
generated abelian group with no finite quotient, hence zero.  So every basis
vector satisfies `e_x = sum_r c_(r,x) E_r` for some integers.  Fix such
integers and put `C_G = max_x sum_r |c_(r,x)|`.

**Theorem (FIC).**  Let `u = (u_x)_(x in X)` be unitaries in `U(k)`, for any
`k`, such that the group `Gamma = <u_x>` is **finite**.  Put
`delta = max_r ||r(u) - 1||_op`.  If `delta < 1/2`, then

```text
max_x ||u_x - 1||_op <= C_G delta.                      (FIC)
```

The threshold `1/2` and the constant `C_G` depend on neither `k` nor
`|Gamma|`.

**Higman.**  For `Hig = <g_0..g_3 | g_i g_(i+1) g_i^(-1) g_(i+1)^(-2)>`
the `i`-th relator has exponent sum `-e_(i+1)`, so `C_Hig = 1`.  Hence for
finite-image tuples with `delta < 1/2`,

```text
max_i ||u_i - 1|| <= max_i ||u_i u_(i+1) u_i^* - u_(i+1)^2||.
```

Equivalently, on every finite-image tuple the Higman defect `D` satisfies

```text
D(u) >= min(1/2, max_i ||u_i - 1||).                    (FIC-D)
```

**Corollary for (CGC).**  If `C_i Z_(i+1) C_i^* = Z_(i+1)^2` exactly and
`||Z_(i+1) - C_(i+1)|| <= eta`, then the Higman defect of `(C_i)` is at most
`eta + 2 eta = 3 eta`.  So if `<C_0,..,C_3>` is finite and `eta < 1/6`, then
`max_i ||C_i - 1|| <= 3 eta`.

The proof is in `finite-image-higman-models-collapse-opnorm-proof` and is
self-contained.  It uses only the commutator estimate
`||[s,t]-1|| <= 2||s-1|| ||t-1||`, the discreteness of finite groups, the
existence of a non-central abelian normal subgroup in a non-abelian nilpotent
group, and the orthogonal isotypic decomposition of a unitary representation
of a finite abelian group.

## What this kills (class obstruction)

Invariant: the **discreteness gap** `m_Gamma = min_(g != 1) ||g - 1|| > 0`,
fed into a Zassenhaus contraction.  In any finite-image model with defect
below `1/2`, the defect elements `w_i` lie in the nilpotent normal subgroup
`<S_delta>`.  The step where every member dies is the finite quotient
`Gamma / <S_delta>`, and then the finite permutation image on Clifford
isotypic components.  Hig must kill both, because it has no finite quotient.

So every countermodel to (HMF5), to (CGC) or to (PUC) must generate an
**infinite** subgroup of `U(k)`, at every stage of the sequence with
`delta < 1/2`.  Among the ansaetze this excludes are:

- monomial and permutation-diagonal models, and every root-of-unity clock;
- Clifford and Weil-group models, meaning finite Fourier transforms, chirps,
  dilations `e_x -> e_(ax)` and Heisenberg translations over `Z/q`;
- images of finite groups of Lie type and of any finite group representation;
- every HOC-type clock from
  `periodic-higman-bs-clocks-have-three-opnorm-small-seams` whose matcher
  `H_n` generates, with `P_n` and `D_n`, a finite group.  There the
  conjugators have norm distance `2` from `1`, so by (FIC-D) the four
  Higman defects have maximum at least `1/2`.  Equivalently, the four
  seams have maximum at least `1/6`.

A countermodel must therefore use matrices whose generated group has
irrational or non-algebraic "angles": for example the joint-commutant torus
regauges now being probed live, with generic phases.  (FIC) says nothing
about those, and (CGC) stays OPEN.

## Numerical sanity check (not part of the proof)

`experiments/finite-image-collapse-2026-09-17/check_finite_image_collapse.py`
samples tuples and runs a greedy search inside three groups: monomial groups
(`n <= 9`, `q <= 27`), HOC clocks over `Z/q` with monomial matchers
(`q <= 27`), and Clifford/Weil groups over `Z/p` (`p <= 7`).  The search
minimizes `D(u) - min(1/2, max ||u_i - 1||)`.  The smallest margin it found
was `sqrt(2) - 1/2 = 0.9142`: every nontrivial tuple it reached had defect
at least `sqrt(2)`.  That is consistent with (FIC-D), and suggests the
threshold `1/2` is far from sharp in practice.
