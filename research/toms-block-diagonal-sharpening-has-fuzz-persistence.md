---
rg: 2
id: toms-block-diagonal-sharpening-has-fuzz-persistence
kind: claim
title: In Toms's tower a copy-block-diagonal near projection that tracks the block traces of a pushforward within C lines has a point where every block is half fuzzy
distinct_from:
  toms-twisted-swap-pairs-are-totally-degeneracy-forcing: that shows transports between twisted halves are useless in uniform 2-norm; this shows that rounding with no transport between copies cannot sharpen, unless some blocks move by a macroscopic number of lines.
  toms-rank-bookkeeping-admits-monotone-realizer-profiles: that shows integer rank data never obstruct; this is the 2-norm, fractional-trace counterpart, where a degree argument does obstruct bounded-displacement rounding.
  toms-schubert-algebra-continuous-ranks-are-constant: that is the rigidity conjecture; this proves its fuzz-persistence heuristic for block-diagonal rounding with bounded displacement, and corrects the hypersimplex signpost there.
---

Let `A = lim (A_L, phi_L)` be the non-simple limit of Toms's Section 4
(arXiv:2606.12188v2). For `M > L`, `phi_(L,M)(q_L^(direct_sum k))` is the
orthogonal sum of `K = 2^(M-L)` copy projections `Q_i`, where `Q_i` is the
pullback of `q_L^(direct_sum k)` along the copy map `z -> z^(i)`, twisted by a
line bundle. "Lines" means unnormalized fibre trace `Tr`.

**Theorem.** Let `z in M_k(A_L)` be a positive contraction, put
`x(y) = Tr z(y)` for `y in X_L`, and let `[a, b]` be the range of `x`. Let
`C >= 0` with `b - a > 4C + 2`. Let `e = sum_i e_i in M_k(A_M)` be a positive
contraction with `e_i = Q_i e Q_i` (block-diagonal), and suppose

```text
| Tr e_i(w) - x(w^(i)) | <= C      for every w in X_M and every i.
```

Then some `w in X_M` has `Tr e_i(w) in Z + 1/2` for **every** `i`, so

```text
Tr (e - e^2)(w) >= K/4,    i.e.   normalized defect  tr(e - e^2)(w) >= 1/(4 k r_L).
```

This is the worst-point defect of a copy-diagonal pushforward of a single
fuzzy line per copy. So bounded-displacement block-diagonal rounding never
sharpens.

**Consequences.**
- *Correction to the signpost in*
  `toms-schubert-algebra-continuous-ranks-are-constant`. That signpost rounds
  one fuzzy line per copy by a vertex-fixing map `[0,1]^M -> [0,1]^M` of the
  hypersimplex, with integer parts frozen. Its displacement is at most `1`
  line per copy. By the theorem with `C = 1`, no such rounding extends
  continuously across the walls where integer parts change, once the trace of
  `z` has range above `6` lines. The heuristic "2-norm coherence can probably
  be rounded copy-diagonally" does not follow.
- *What remains possible.* A uniformly 2-norm-Cauchy sharpening allows
  `sum_i |Tr e_i - x_i|^2 <= delta^2 K r_L^2`, so a small fraction of blocks can
  move by a macroscopic fraction of `r_L` lines. A sharpening must either move
  such **whole-copy mass** or be non-block-diagonal, i.e. transport between
  twisted copies, where `toms-twisted-swap-pairs-are-totally-degeneracy-forcing`
  applies to transports made uniformly across copies.

**Model test.**
- *The displacement bound is load-bearing.* Without it, prefix filling
  `Tr e_i = min(r_L k, max(0, sum_j x_j - (i-1) r_L k))` in a fixed block order is
  continuous and leaves at most one fractional block, but moves blocks by up to
  `r_L k` lines.
- *The range bound is load-bearing.* If `x` is constant, `e = phi(z)` rounded
  once by a constant shift has integer block traces everywhere.
- *Real object.* In Toms's tower, the ramp through a fixed chain of lines with
  level `r_L F_L - 2` has range about `r_L (max h - min h)`. That exceeds `4C + 2`
  at deep stages for any fixed `C`.

Proof: `toms-block-diagonal-sharpening-fuzz-persistence-proof`. Internal
derivation, unreviewed. It uses independence of copy coordinates only, not the
twists.
