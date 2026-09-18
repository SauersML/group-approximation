---
rg: 2
id: slit-origami-z2-pair-has-rank-distance-half-l
kind: claim
title: The slit origami pair with commutator rank two is at rank distance exactly floor(L/2) = Theta(sqrt d) from commuting pairs, so bounded-rank stability of Z^2 loses at least sqrt(d/8)
distinct_from:
  slit-origami-z2-pair-needs-logarithmic-rank-to-commute: same pair, but that node proves a rank lower bound of order log L through extremal length (and a sharp Theta(log L) Hilbert--Schmidt distance); this node computes the rank distance exactly, floor(L/2), by an area-over-perimeter monodromy count, which refutes the log-loss form C(k) log d left open there.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung for Deligne sector tuples; this pins the exact dimension loss of its commuting-pair rounding input for Z^2 at sqrt d.
  almost-commuting-permutations-are-near-commuting: that is normalized Hamming stability of Z^k; this is unnormalized rank distance with commutator rank two, where the normalized statement gives no bound.
artifacts:
  - research/slit-origami-z2-pair-has-rank-distance-half-l-proof.md
  - experiments/slit-origami-rank-distance-2026-09-17/check_rank_distance.py
  - experiments/slit-origami-rank-distance-2026-09-17/check_rank_distance.out
---

**ESTABLISHED (unreviewed)** (`slit-origami-z2-pair-has-rank-distance-half-l-proof`).
This settles the rank question behind bus need `e4b93e48`.

**Setting.** This is the slit origami of `slit-origami-z2-pair-needs-logarithmic-rank-to-commute`. Take
`L >= 2` and `s = floor(L/2)`. The squares are `(i,x,y)` with `i` in `{0,1}` and `x,y` in `Z/L`,
so `d = 2L^2`. The permutations are:

- `sigma(i,x,y) = (i,x+1,y)`;
- `tau(i,x,y) = (1-i,x,1)` if `y = 0` and `0 <= x < s`, and `(i,x,y+1)` otherwise.

`b` and `c` are their permutation matrices, and `rank(bcb^(-1)c^(-1) - I) = 2`.

**Theorem.** Let `m >= 0`, let `beta, gamma` be in `U(m)`, and let `b', c'` be commuting unitaries on
`C^d (+) C^m`. Then

```text
rank(b' - b (+) beta) + rank(c' - c (+) gamma)  >=  floor(L/2).
```

The bound is attained with `m = 0`, `b' = b`, and `c'` the unslit shift `(i,x,y) -> (i,x,y+1)`.
So the minimal rank distance of `(b,c)` to commuting pairs is exactly `floor(L/2)`, which is at least
`sqrt(d/8) - 1/2`.

**Proof idea.**

- The rectangle word `W = c^(-s) b^(-s) c^s b^s` is trivial on every commuting pair.
- On the origami, `W` returns each square to its base square. It changes the sheet exactly on the
  `2s^2` base squares whose `s x s` loop crosses the slit an odd number of times. So
  `rank(W(b,c) - I) = 2s^2`. This is an area count.
- Telescoping `W(b,c) - W(b',c')` gives `4s` terms. Each term has rank `rank(b'-b)` or `rank(c'-c)`,
  so the total rank is at most `2s (rank(b'-b) + rank(c'-c))`. This is a perimeter count.
- Area over perimeter gives `s`.

**Consequences.**

- **Loss at least `sqrt d` at `k = 2`.** Let `f(k,d)` be any function such that `rank([b,c] - I) <= k`
  in dimension `d` forces a commuting pair within rank `f(k,d)`. Then `f(2, 2L^2) >= floor(L/2)`.
  This refutes every form `C(k) log d` and every form `C(k) d^alpha` with `alpha < 1/2`, even when
  padding is allowed. The `log`-loss route of `slit-origami-z2-pair-needs-logarithmic-rank-to-commute`
  is dead.
  - Rank and Hilbert--Schmidt distance separate sharply. For the same pair the HS^2 distance is
    `Theta(log L)`, while the rank distance is `Theta(L)`.
- **What survives for the Deligne rung.** Suppose a bound `f(k,d) <= C(k) sqrt d` holds. (LOC) is
  linear in `d`, so it would still close the joint-spectrum step:
  `d <= (1+A_g)k + N_g C(k) sqrt d` gives `d <= 2(1+A_g)k + N_g^2 C(k)^2`. So `sqrt d` is now the
  exact threshold.
  - If some family with bounded commutator rank needs rank distance `>= c d`, no rounding at any
    sublinear cost exists, and joint spectra cannot be formed by rounding.
  - If every such pair is within `C(k) sqrt d`, the rung survives.
- **Why a slit is the worst for this word family.** A single defect pair at distance `r` apart
  costs rank at most `r` (cut along the slit). The loop count certifies at least the side length of
  the largest square that fits between the defects. On a `d`-dimensional two-sheeted torus both are
  `<= sqrt(d/2)`. A linear lower bound would need a different geometry, such as expander-like base
  graphs, where monodromy area grows linearly in perimeter. That is the falsifiable next test.

**Mechanism, and why it succeeds where the extremal-length count stalled.** Hilbert--Schmidt mass
can spread thinly over the whole surface. The ring-by-ring estimate therefore only sees extremal
length, and the log is sharp there. Rank cannot spread. A rank-`D` perturbation changes the value
of a length-`N` word by rank at most `ND`, while the monodromy of the word is a permutation whose
rank defect equals the number of enclosed base squares. Counting dimension, rather than energy,
turns the isoperimetric ratio into the bound.
