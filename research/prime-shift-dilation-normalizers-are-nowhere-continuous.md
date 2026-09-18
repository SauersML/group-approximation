---
rg: 2
id: prime-shift-dilation-normalizers-are-nowhere-continuous
kind: claim
title: A permutation of Q that shifts the primes on the dilation group is c*sigma on each half-line and is discontinuous at every nonzero point for the real topology and everywhere for every p-adic topology
distinct_from:
  gl-n-q-lies-in-prime-shift-permutation-group: that uses one particular prime shift sigma; this proves every permutation inducing such a shift on the dilation group is sigma up to two constants, and is discontinuous everywhere, so no tamer version exists.
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that excludes piecewise-linear hosts acting on GL_n(Q) linearly; this excludes a single element that normalizes the dilations by a prime shift, in any topological host where it would have to be continuous at one point.
---

**ESTABLISHED (2026-09-18)** through
`prime-shift-dilation-normalizers-are-nowhere-continuous-proof`. Lane proof,
not independently reviewed; elementary.

**Setup.**
- `D = {m_a : x -> a x, a in Q_>0}` is the group of positive dilations of `Q`.
- `β` is an automorphism of the multiplicative group `Q_>0` that permutes the
  primes with no fixed prime. Every shift along a `Z`-indexing of the primes is of
  this kind.
- `π in Sym(Q)` satisfies `π m_a π^-1 = m_(β(a))` for all `a in Q_>0`.

**Statement.**
1. **Rigidity.** `π(0) = 0`, and there are `c_+ = π(1)`, `c_- = π(-1)` with
   `π(x) = c_+ β(x)` for `x > 0` and `π(x) = c_- β(-x)` for `x < 0`. So, up to
   these two constants, `π` is the given prime shift on each half-line.
2. **Real topology.** `π` is discontinuous at every point of `Q^x`.
3. **p-adic topologies.** For every prime `p`, `π` is discontinuous in the
   `p`-adic topology at every point of `Q`, including `0`.
4. **Consequence (question 4 of the coordinator).**
   - No permutation that is continuous at even one point of `Q^x` for the real or
     some `p`-adic topology can conjugate the dilation group by a shift of the
     primes.
   - In particular, no piecewise-affine, piecewise-projective or Cantor-model map
     does.
   - So a tamer substitute for `σ` must give up normalizing `D`. It has to carry
     `m_2` to `m_p` by conjugators that do not normalize `D`, possibly different
     conjugators for different `p`.
   - Example: `φ_p(2^j y) = p^j (1 + (p-1)(y-1))` for `y in [1,2)` satisfies
     `φ_p(2x) = p φ_p(x)` on `Q_>0`, and is piecewise affine with pieces
     accumulating only at `0` and `∞`.
   - Whether finitely many such maps and `Aff(Q)`-type generators produce all the
     `φ_p` is not examined. Nor is whether attempts 2, 10 or 14 of the root already
     exclude the resulting groups.
