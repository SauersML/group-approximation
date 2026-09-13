# Lane solve-hyperbolic-rf: residual finiteness of hyperbolic groups (2026-09-13)

Target: `non-residually-finite-hyperbolic-group`, i.e. Gromov's question. It stays
OPEN. This lane adds:
- a sharpened no-small-quotient theorem;
- a proof that first-moment counting cannot go further in the density model.

Nothing here has been independently reviewed.

## 1. The graph on main (read 2026-09-13 at 46dd14831)

**Equivalent forms, all established:**
- `kapovich-wise-rf-iff-finite-quotients`;
- `hyperbolic-rf-question-equals-vtf-question`;
- `hyperbolic-rf-vtf-kazhdan-equivalence`;
- `hyperbolic-rf-question-reduces-to-one-fixed-host`, where one Sp(2,1) lattice suffices;
- `finite-simple-spectrum-gives-quotientless-hyperbolic-group`;
- `convergent-quotient-count-decides-gromov-question`.

**Live routes on the root:**
- from a nonsofic hyperbolic group;
- relative Dehn filling;
- a persistent central extension;
- a Rips kernel;
- the random complex, which needs `random-complex-group-no-large-finite-quotients` (OPEN).

**Dead routes:** compression transplant, free-lamp compression, Oyakawa graph wreaths,
Hull routing, and the periodic-Higman fillings.

**Candidate classes under `hyperbolic-simple-triangle-group-without-finite-quotients`:**
- the (A_7, A_7, A_8) triangles;
- the CCKW (6,6,8) cores;
- the Kazhdan SL_2 root triangles.

**Counting on main:** `random-relators-kill-small-simple-quotients-of-kazhdan-groups`
(threshold `λ^(-L)` at bounded `k`) and `density-random-groups-no-small-nondegenerate-almost-reps`.

**Kapovich–Wise pin.** `kapovich-wise-rf-iff-finite-quotients-citation` already pins
Theorem 1.2 (J. Algebra 223 (2000), p. 565) against the published paper, read
2026-09-11. It was not re-read here.

## 2. New results

1. `density-random-groups-no-finite-quotients-below-exp-k`, with route
   `density-random-no-quotients-below-exp-k-letter-swap-proof`.
   - **Per-homomorphism bound.** A uniform set of `k` cyclically reduced relators of
     length `L` in `F_m` lies in the kernel of a given homomorphism that is non-constant
     on letters with probability at most `(1 − κ_m)^k`, where `κ_m = (m−1)/(2m(2m−1)^3)`.
   - **Union bound.** Summing over simple groups by order, at most two per order, gives no
     nontrivial finite quotient of order `<= exp(κ_m k/(2(m+1)))` with probability
     `>= 1 − 2e^(−κ_m k/2)`, for odd `L`.
   - **Density.** At density `d ∈ (1/3, 1/2)` and `L` an odd multiple of 3, with
     probability tending to 1 the group is hyperbolic, Kazhdan, torsion-free and has
     `b_2 >= 1`, and it has no nontrivial finite quotient of order
     `<= exp(κ_m (2m−1)^(dL)/(2(m+1)))`. That is doubly exponential in `L`; the thresholds
     already on main are singly exponential.
   - **Without the coincidence import.** The weaker bound `M^((m−1)M+2)(1−κ_m)^k`
     still reaches order about `κ_m k / log k`.
2. `finite-simple-groups-at-most-two-per-order`, with route
   `finite-simple-groups-order-coincidence-citation` (a literature import, quoted in §4).
3. `density-random-simple-quotient-first-moment-diverges`, with route
   `density-random-first-moment-divergence-proof`.
   - **Statement.** For `0 < d < 1/2` and large `L ≡ 3 (mod 6)`, the expected number of
     finite simple quotients is infinite.
   - **Where it comes from.** Relator sets built from products of three conjugates of
     `a_1^3` sit in the kernel of `F_m ->> A_n` for every odd `n >= 5`, all with one
     positive probability.
   - **Why it is a barrier.** Those members are not Kazhdan. After conditioning on
     non-elementary hyperbolicity, (C2) of `convergent-quotient-count-decides-gromov-question`
     shows that a finite conditioned expectation would already give a quotientless
     hyperbolic Kazhdan group. So the first moment either diverges or is at least as
     strong as the target.

Attempts bullet added to `hyperbolic-group-without-finite-quotients`.

## 3. Exact checks on MSI

- **Run.** Host ahl02, `/usr/bin/python3.12` (3.12.13), 23.7 s.
- **Files.** Script `experiments/hyperbolic-rf/density_quotient_checks.py`
  (md5 `39bc35c4e9206a9268917cb1a8b9e31e`), output
  `experiments/hyperbolic-rf/density_quotient_checks.json`
  (md5 `17bffe6e71b6ca9420814a0d07e68702`, `ALL_OK: true`).
- **(a)** `C_L` formula, for `m = 2` with `L = 3..11` and `m = 3` with `L = 3..7`: 14/14 match.
- **(b)** `T^n` formula, for `m = 2, 3, 4`: holds.
- **(c)** Window bound (W) at the same sizes: 14/14 hold.
- **(d)** `P[φ(w) = 1] <= 1 − κ_m` for non-constant `φ`: 0 violations.
  - Cases: all of `F_2 -> S_3` (`L = 3..7`), all of `F_2 -> S_4` (`L = 5..7`), all of
    `F_3 -> S_3` (`L = 5`), and 150 random `F_2 -> A_5` (`L = 7`).
  - The largest observed value is 0.619, against the bound `107/108 ≈ 0.991` for `m = 2`.
    The bound is crude and was not optimised.
- **(e)** `⟨(1 2 3), (1 ⋯ n)⟩ = A_n` for `n = 5, 7, 9`.
- **(f)** The three-conjugate words for `(m, r) = (2,2), (2,3), (3,2)` are distinct and
  cyclically reduced, and meet the counting bound.

## 4. Source pin

Wikipedia, *List of finite simple groups*, raw wikitext fetched on MSI on 2026-09-13,
md5 `5266becea6bdcd211217714681a7ec7b`, line 8:
"no two finite simple groups have the same order, except that the group A8 = A3(2) and
A2(4) both have order 20160, and that the group Bn(q) has the same order as Cn(q) for q
odd, n > 2." The markup is stripped here; the citation route quotes it verbatim.

## 5. Exact gap

- **Counting.** It excludes finite quotients of a density random group only below order
  `exp(c k)`. Beyond that the unconditioned moment is infinite, and the conditioned one
  is as strong as the target.
- **Negative answer.** It needs structural control of the large simple quotients of a
  typical member: Lie-type families from infinite-image representations, and large
  alternating quotients. Property (T) doesn't bound those
  (`caprace-kassabov-hyperbolic-kazhdan-alternating-quotients`).
- **Positive answer.** It needs cocompact cubulation or another RF mechanism beyond
  density `1/6`. None is known.
