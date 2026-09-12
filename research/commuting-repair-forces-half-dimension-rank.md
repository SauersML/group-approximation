---
rg: 2
id: commuting-repair-forces-half-dimension-rank
kind: claim
title: Repairing the clock and shift to commuting unitaries moves at least half the dimension in rank, at any padding
distinct_from:
  atlas-three-label-mode-small-phase-weyl-hits-commutative-wall: that computes the limiting moments of the Atlas three-label unitary built from a clock-shift pair and places it behind the commutative fence; this is a rank lower bound for any commuting correction of the pair itself, with arbitrary padding allowed.
  exel-loring-relative-quasirep-invariant: that records the homological Bott-type invariant obstructing operator-norm repair of an almost commuting pair; this concerns a regime where Hilbert-Schmidt repair does exist and bounds the rank any such repair must use.
  bs14-low-rank-boundary-surgery-preserves-the-regular-face: that cuts an already exposed low-rank boundary and computes what survives, a forward operation; this proves that no scheme confined to sublinear-rank corrections can repair a general small-defect input.
artifacts:
  - research/artifacts/retained-core-and-rank-countertests-2026-09-08.md
---

**ESTABLISHED.**  For `d >= 2` let `zeta = e^(2 pi i / d)` and let `U, V` be the
clock and shift, `U e_j = zeta^j e_j`, `V e_j = e_(j + 1 mod d)`.  Then
`U V = zeta V U` and

```text
||U V U^* V^* - I||_(2,d) = 2 sin(pi / d) -> 0.                         (CR1)
```

Let `k >= 0` be arbitrary, `A, B in U(k)`, `U_0 = U (+) A`, `V_0 = V (+) B`, and
let `U^, V^ in U(d + k)` be any commuting unitaries.  Then

```text
rank(U_0 - U^) + rank(V_0 - V^) >= d / 2.                              (CR2)
```

The bound does not improve with `k`: no amount of padding lets a sublinear-rank
correction commute this pair.  In particular a correction
`U^ = exp(i K_U) U_0`, `V^ = exp(i K_V) V_0` with each `K` supported on the
off-diagonal blocks between the old space and the added one has rank at most
`2k` and therefore forces `k >= d / 8`.

**And yet the pair is repairable in the normalized metric.**  With `d = q^3`,
split the cycle into `q` consecutive blocks of length `q^2`, let `U'` be
constant on each block equal to the first clock value there and `V'` the cyclic
shift within each block.  They commute, and

```text
||U - U'||_(2,d) <= 2 pi / q,     ||V - V'||_(2,d) = sqrt 2 / q,
rank(U - U') = d - q.                                                   (CR3)
```

**Consequence.**  Small normalized-Hilbert-Schmidt motion and small-rank
surgery are different resources, and the repair may be forced to use the first
across almost every direction.  A completion theorem that only permits
corrections supported on the added block together with a sublinear surgery
subspace is therefore too restrictive to be the general mechanism, whatever
padding it allows.

Scope: this example is about `Z^2`, which is flexibly Hilbert-Schmidt stable.
It is evidence about the admissible *shape* of a repair theorem and about
nothing else; it is not evidence for or against any approximation property of a
group.
