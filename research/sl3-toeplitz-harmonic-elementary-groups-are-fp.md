---
rg: 2
id: sl3-toeplitz-harmonic-elementary-groups-are-fp
kind: claim
title: For infinitely many N, the elementary group E_N(R_T) of the SL_3(Z) Toeplitz harmonic ring is finitely presented
distinct_from:
  sl3-toeplitz-harmonic-pe-groups-are-simple: that proves PE_N(R_T) simple with centre of order at most 2, and reduces its finite presentation to this claim; this is the finite-presentation claim itself.
  sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget: that is the K-theoretic necessary part (R1, R2); this is finite presentation, which implies both.
  q-algebra-with-fp-simple-projective-elementary-group: that is the host premise for all rings containing Q; this is its instance for R_T.
---

**OPEN.** Let `R_T` be the ring of `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`. For
infinitely many `N >= 3`, `E_N(R_T)` is finitely presented.

With `sl3-toeplitz-harmonic-pe-groups-are-simple`, this gives the host premise
`q-algebra-with-fp-simple-projective-elementary-group` for `R_T`, through
`q-algebra-host-via-sl3-toeplitz-harmonic-ring`, and hence the root
`gl-n-q-embeds-in-fp-simple-group`.

## Necessary conditions (landed)

- **(R2).** The Steinberg symbols of commuting units generate a finitely generated subgroup of
  `K_2(R_T)` (`infinitely-generated-symbols-block-fp-elementary-groups`).
- **(R1).** Every nonzero idempotent corner `e R_T e` sends `K_2(Q)` to a finite group
  (`full-corners-must-kill-rational-k2-symbols`).
- Both are recorded, with what is known, in `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`.
- The centre clause holds: `Z(E_N(R_T)) ⊆ {±I}`.

## Route to a proof

- If `R_T` is a finitely presented ring and `N >= 4`, then `St_N(R_T)` is finitely presented. This is
  the statement quoted in `steinberg-finite-presentation-and-kazhdan-theorem` (Krstić–McCool).
- `projective-elementary-fp-kernel-criterion` then reduces the claim to finite normal generation of
  `K_2(N, R_T) = ker(St_N(R_T) -> E_N(R_T))`.
- Whether `R_T` is finitely presented as a ring is not recorded on main. Its relations include the
  subshift's forbidden words and the harmonic function's elimination identities, which may be
  infinitely many.

Owner of finite presentation: lane `gq-steinberg-q`. This node was placed by lane `gq-en-ring` as the
open target.
