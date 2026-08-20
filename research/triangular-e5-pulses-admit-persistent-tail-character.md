---
rg: 2
id: triangular-e5-pulses-admit-persistent-tail-character
kind: claim
title: A single additive tail character detects every triangular E5 pulse
artifacts:
  - experiments/e5_persistent_tail_character.py
distinct_from:
  fanizza-symmetric-kernel-has-two-root-e5-clock: that proves every pulse has a fresh unique leading coefficient; this proves that triangularity does not make that coefficient the character's first detection.
  free-root-first-detection-eigenvectors-localize-exactly: that is correct under an explicit first-detection hypothesis; this shows the hypothesis is not supplied by the pulse degree calculation.
  free-root-top-boundary-reservoir-is-summable: that sums genuine first-detection layers; this constructs one character which responds at infinitely many pulse levels while belonging to one early first-detection layer.
---

Let `p_n in F_2[x]` be the `e_02` component of the symmetric Fanizza/E5
hard pulse at level `n>=1`.  The clock calculation gives

```text
deg p_n=2n,              [x^(2n)]p_n=1.               (PTC1)
```

There is an additive functional `ell:F_2[x]->F_2` such that

```text
ell(p_n)=1                 for every n>=1.             (PTC2)
```

Construct it recursively.  After choosing `ell` below degree `2n`, set its
value on the fresh monomial `x^(2n)` so that `(PTC2)` holds at level `n`.
Equation `(PTC1)` ensures that this never changes an earlier pulse value.
Thus `chi(f)=(-1)^ell(f)` is negative on every pulse even though its first
nonzero coefficient occurs at degree at most two.

The obstruction already exists in exact finite models at every fixed depth.
For `N`, choose `m>2N`, read the first `m` dual bits of `ell` as a character
of the additive group of `R_m=F_2[x]/(x^m-1)`.  No pulse
`p_1,...,p_N` wraps, so all have value `-1`.  The elementary transporter is
invertible over the finite ring `R_m`; inducing the root character through
the resulting finite group gives an exact finite-dimensional representation
containing that eigencharacter.

Consequently, a unique top monomial or strictly increasing pulse degree does
not put pulse-negative mass in distinct Fourier boundary layers.  One must
additionally force lower-root triviality, construct a prefix survivor, or use
a genuinely one-sided noninvertible degree shift.

The verifier constructs the functional through depth 64.  Its support begins
`2,6,14,30,62,126`, and all 64 pulse evaluations equal one.
