---
rg: 2
id: z2-commuting-pairs-are-not-bounded-rank-stable
kind: claim
title: Z^2 is not bounded-rank stable, because a dislocation dipole on the n x n torus has commutator rank 2 but is rank n/32 from every commuting pair
artifacts:
  - experiments/bounded-rank-z2-dislocation-2026-09-17/dislocation.py
  - experiments/bounded-rank-z2-dislocation-2026-09-17/results.txt
distinct_from:
  almost-commuting-permutations-are-near-commuting: that is stability of the commutator in the normalized Hamming metric (defect delta d gives distance epsilon d); this shows the uniform version, with bounded defect and bounded distance, fails, even for permutation matrices and over every field.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung for the Deligne covers; this refutes the Z^2 black-box input that the joint-spectrum route to it needed.
---

**ESTABLISHED** (`z2-commuting-pairs-are-not-bounded-rank-stable-proof`). Unreviewed.

**Theorem.** For `n >= 8` with `4 | n` and `d = n^2` there are permutation matrices `A, B` in `U(d)` with
`rank(AB - BA) <= 3` such that every commuting pair `A', B'` in `GL_d(F)`, over any field `F`, has

```text
max( rank(A - A'), rank(B - B') ) >= (n - 4) / 32.
```

Undoing one interval twist gives a commuting pair at rank distance `n/2 + 1`. So the distance is
`Theta(sqrt d)` while the commutator defect stays bounded, and the same holds for `Z^N`, `N >= 2`
(extend by identities).

**Construction (a dislocation dipole).** On `X = Z/n x Z/n`, `alpha` is the horizontal shift.
`beta` is the vertical shift, except across the row transition `n-1 -> 0`, where the columns
`[n/4, 3n/4]` are cyclically shifted by one. The two ends of that interval are edge dislocations with
opposite Burgers vectors `+-e_1`.

**Invariant behind the bound.** Put `w_L = a^L b^L a^(-L) b^(-L)` and `phi(L) = rank(w_L(A,B) - I)`.
- For a pair within rank `C` of a commuting pair, `phi(L) <= 4 L C` (a linear law).
- `w_L` is a product of `L^2` conjugates of `[a,b]^(+-1)`, so `phi(L) <= L^2 rank([A,B] - I)` always
  (the area law).
- The dipole saturates the area law up to a constant: the loop from every start point in an
  `(L-1) x L` block around one core fails to close by one step.

So bounded-rank closeness to commuting is detected by the growth of `phi`, and dislocations make it
quadratic.

**Computation.** `experiments/bounded-rank-z2-dislocation-2026-09-17/dislocation.py` builds the pair
for `n = 8..64`. It checks that `AB` and `BA` differ at exactly 3 points, that the exact rank of `AB - BA`
over `Q` is 2, and that `rank(w - I) = n^2/8`, which gives the bound `C >= n/8` at `L = n/4`
(`results.txt`).

**Consequence for the Deligne rung.** The atom-level route in
`research/artifacts/deligne-bounded-rank-torsion-spectrum-2026-09-17.md` (Part II) needed a joint
spectral measure for the long-root pair of a rank-`k` sector tuple, and posted the need "rank
`[b,c]` bounded implies within rank `C(k)` of commuting". That need is false. Any proof that uses
the long-root pair must rule out dislocation-type configurations (quadratic `phi`). It can only do
that through the `SL_2(Z)` or `Sp_(2g)(Z)` conjugation relators, never through `Z^2` alone.
