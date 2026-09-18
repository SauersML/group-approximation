---
rg: 2
id: no-four-strand-bigelow-arc-pair-with-at-most-250-crossings
kind: claim
title: Every Bigelow arc pair of type (q1 to q2, p0 to q3) on the 4-punctured disk has more than 250 crossings
distinct_from:
  burau-kernel-avoids-short-point-pushing-braids: that claim bounds the free length of a kernel word in K_4; this claim bounds the geometric intersection number of the arc pair that any kernel element produces, which is an unrelated complexity and covers all of B_4
  four-strand-burau-representation-has-nontrivial-kernel: that claim is existence of a kernel element; this claim is a finite exclusion that any kernel element must defeat
artifacts:
  - research/artifacts/burau-four-strand-bigelow-arc-search-2026-09-17.md
  - experiments/burau-arc-orbit-search-2026-09-17/arcfast2.c
  - experiments/burau-arc-orbit-search-2026-09-17/arcpairs_np.c
  - experiments/burau-arc-orbit-search-2026-09-17/run.sh
---

**Setup.**

- `D_4` is the disk with punctures `q_1, ..., q_4` and a basepoint `p_0 ∈ ∂D_4`.
- `alpha_0` is the straight arc from `q_1` to `q_2`, and `beta_0` is the straight arc from `p_0` to `q_3`.
- For arcs `alpha` and `beta`, `<alpha, beta> ∈ Z[t^{±1}]` is Bigelow's pairing (GT 3 (1999), Definition 1.3). Summing over the lifts `t^k beta~`, it records the algebraic intersection numbers of `alpha~` with those lifts.

**Claim.** Let `alpha` be an embedded arc from `q_1` to `q_2` in minimal position with `beta_0`. If `1 <= i(alpha, beta_0) <= 250`, then `<alpha, beta_0> != 0`.

**What it rules out.**

- Bigelow's proof of the "only if" half of Theorem 1.4 shows the following:
  - Every braid `psi` in the kernel of the 4-strand Burau representation has `<psi(alpha_0), beta_0> = 0`.
  - If `psi != 1`, some conjugate `psi'` of `psi` (also in the kernel) is such that `psi'(alpha_0)` cannot be homotoped off `beta_0`. Otherwise `psi` would fix every straight arc, so it would be a power of the boundary twist, and Burau sends that twist to `t^4 I`.
- By this claim, for every braid `psi` in the Burau kernel, `i(psi(alpha_0), beta_0)` is either 0 or greater than 250.
- Hence a No answer to Zaremsky Problem 3.5 needs a kernel braid that pushes `alpha_0` across `beta_0` more than 250 times.
- Bigelow states a bound of 500 from an unpublished search, with no code or method. This claim gives a reproducible, exhaustive replacement for that bound up to 250, over the full configuration space rather than a restricted family of arcs.

**Proof.** Exhaustive enumeration of the crossing sequences of `alpha` in `D_4` cut along `beta_0`, modulo homeomorphisms preserving `beta_0`, with an exact pairing polynomial and `l^1` pruning. The run finds no vanishing pairing for any `m <= 250`. Details are in `no-four-strand-bigelow-arc-pair-with-at-most-250-crossings-proof` and the artifact.
