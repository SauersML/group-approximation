# Burau kernel search in the point-pushing subgroup K_4, free length ≤ 24

Lane z3-05-burau-search, 2026-09-13. Problem: Zaremsky 3.5, the No side
(`four-strand-burau-representation-has-nontrivial-kernel`). Script:
`research/artifacts/zp-burau-k4-kernel-search-2026-09-13.py`.

## Setup

- **Burau convention.** `rho_4: B_4 -> GL_4(Z[t, t^{-1}])` sends `sigma_i` to
  the identity with the block `[[1-t, t], [1, 0]]` in rows and columns
  `i, i+1`. The block for `sigma_i^{-1}` is `[[0, 1], [t^{-1}, 1 - t^{-1}]]`;
  their product is `I`.
- **The group.** `K_4` is the kernel of forgetting strand 4, restricted to
  the pure braid group. It is free on
  - `A_{14} = sigma_3 sigma_2 sigma_1^2 sigma_2^{-1} sigma_3^{-1}`,
  - `A_{24} = sigma_3 sigma_2^2 sigma_3^{-1}`,
  - `A_{34} = sigma_3^2`.

  It is the point-pushing subgroup of `p_4`, the `K_4` of arXiv:2607.05283,
  and it contains the Brunnian subgroup `Brun_4`.
- **Relevance.** By Long's theorem
  (`burau-faithful-iff-faithful-on-noncentral-normal-subgroup`, established),
  if `ker rho_4 != 1` then `ker rho_4 ∩ Brun_4 != 1`. So every kernel
  element that matters lies in `K_4`.

## Completeness argument

Let `w` be a nontrivial reduced word in the six letters `A_{j4}^{±1}`, with
`|w| ≤ 2L` and `rho_4(w) = I`.

1. Split `w = u v^{-1}` with `|u| = ceil(|w|/2) ≤ L` and `|v| ≤ L`.
2. Because `w` is reduced, `u` and `v` are reduced.
3. `u != v`, since otherwise `w` would freely reduce to `1`.
4. `rho_4(u) = rho_4(v)`.

The script enumerates every reduced word of length `≤ L`. For `L = 12` that
is `1 + 6(5^12 - 1)/4 = 366,210,937` words; the printed level counts are
`6·5^{k-1}`. For each word it computes `rho_4` at `t = 123456789` modulo the
prime `P = 1000000007`. `P` does not divide `123456789`, so the evaluation
is a ring homomorphism, and exact equality of `rho_4(u)` and `rho_4(v)`
implies equal evaluated matrices.

- **64-bit key.** Each evaluated matrix gets a key: a fixed random linear
  combination of its 16 entries, computed in `uint64` arithmetic. The key is
  a deterministic function of the matrix, so equal matrices get equal keys.
  - The keys of all enumerated words are sorted and adjacent equal keys are
    reported.
  - Every reported pair `u, v` is re-checked by exact multiplication over
    `Z[t, t^{-1}]` for the reduced form of `u v^{-1}`.
- **Conclusion.** A run reporting 0 equal keys proves there is no nontrivial
  reduced word of length `≤ 2L` with Burau image `I`. The evaluation step may
  produce false positives, which the exact check removes; it cannot produce
  false negatives.

**Overflow.** Matrix entries are reduced mod `P < 2^30` after every product,
so each entry of a product is a sum of four products below `2^60`, which is
below `2^62`.

## Controls

- **Braid relations.** Mode `control` uses the letters `sigma_1, sigma_2,
  sigma_3` and their inverses as free letters, with `L = 3`. It enumerates
  187 words and reports 56 equal keys. All 56 pairs are exact kernel words
  over `Z[t, t^{-1}]`, e.g. reduced words of length 4 and 6 coming from
  `sigma_1 sigma_3 = sigma_3 sigma_1` and the braid relation. This checks the
  matrices, the key and collision pipeline, and the exact checker.
- **Word counts.**
  - `L = 11`: 73,242,187 words
  - `L = 12`: 366,210,937 words

  Both match the formula for reduced words.

## Run record

Run on MSI acn112/acn116 (sioux) from `/scratch.global/sauer354/zp/z3-05-burau-search/`,
using module `python3/3.10.9_anaconda2023.03_libmamba` (numpy),
`OMP_NUM_THREADS=2` and a 40 GiB virtual-memory cap.

| run | max free length | words | equal keys | exact kernel words | wall time | peak RSS |
|---|---|---|---|---|---|---|
| control, L=3 | 6 (sigma letters) | 187 | 56 | 56 | <1 s | 31 MB |
| k4, L=9 (first script) | 18 | 2,929,687 | 0 | 0 | 2.5 s | — |
| k4, L=10 (first script) | 20 | 14,648,437 | 0 | 0 | 9.8 s | — |
| k4, L=11 | 22 | 73,242,187 | 0 | 0 | 31.7 s | 3.0 GB |
| k4, L=12 | 24 | 366,210,937 | 0 | 0 | 2 min 40 s | 13.8 GB |

The first script (L = 9, 10) evaluated at two primes and used a different
key; the L = 11, 12 runs use the landed script.

Reproduce: `python3 zp-burau-k4-kernel-search-2026-09-13.py k4 12 8 10000`
(about 15 GB RAM).

## Result and scope

- **Result.** No nontrivial element of `K_4` of free length `≤ 24`, in the
  basis `A_{14}, A_{24}, A_{34}`, lies in `ker rho_4`.
- **Scope.**
  - The bound depends on the basis. Brunnian 4-braids are iterated
    commutators in this basis, so only short Brunnian braids are covered.
  - This is not a proof of faithfulness and makes no claim about longer
    words.
  - No comparison with earlier computer searches was done, e.g. Fullarton–Shadrach
    and Beridze–Traczyk, who use other length measures.
  - The computation has not been re-run by a second lane.
- **Next scale.** `L = 13` means about 1.8·10^9 words and needs about 70 GB
  in this layout. Pushing further needs a disk-backed sort or a split by
  first letter.
