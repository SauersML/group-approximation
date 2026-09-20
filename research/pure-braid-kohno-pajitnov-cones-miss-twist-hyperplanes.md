---
rg: 2
id: pure-braid-kohno-pajitnov-cones-miss-twist-hyperplanes
kind: claim
title: "In every affine chart of M_{0,n+1}, a Kohno–Pajitnov positive class is nonzero on every Dehn twist, so positive cones never reach the zero-twist characters of P_n"
distinct_from:
  pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3: that claim proves membership in Sigma^{n-3} for every character with no zero twist value; this shows that the Kohno–Pajitnov positive cones in all charts lie inside that region, so they add nothing to it.
  pure-braid-nonresonant-zero-twist-characters-in-sigma: that claim asks for membership on the twist hyperplanes; this is an obstruction showing one proposed tool (Kohno–Pajitnov in other charts) cannot reach them.
  pure-braid-product-projections-obstruct-bnsr-invariants: that claim puts characters outside Sigma^m; this is about the reach of a membership method, not about Sigma^m itself.
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

Let `n >= 3` and `N = n + 1`. Zero-sum characters of `P_n` are the characters of
`H_n = P_n / Z = pi_1(M_{0,N})`. Write them as `b = (b_xy)` on the pairs of `[N]`,
with `b_ij = a_ij` for `i, j <= n` and every row summing to zero:
`sum_{y != x} b_xy = 0` for each `x`. For a boundary divisor `D_S` of `M̄_{0,N}`
(`2 <= |S| <= N - 2`), put `c_S(b) = sum_{pairs in S} b`. Then `c_S = c_{S^c}`,
and for `S ⊆ [n]` this is the Dehn twist value `c_S(chi)` of the claims on `P_n`.
So the twist hyperplanes of zero-sum characters of `P_n` are exactly the
hyperplanes `c_S = 0`.

Fix distinct `p, q, r` in `[N]` and the chart `z_p = 0, z_q = 1, z_r = ∞`. This
realizes `M_{0,N}` as the complement of an essential affine arrangement in
`C^{N-3}`. Its hyperplanes are the pairs `{x, y} ⊆ T = [N] \ {r}` other than
`{p, q}`, and the meridian of `{x, y}` has value `b_xy`. The chart is
Kohno–Pajitnov positive (arXiv:1101.0437v2, Theorem 2.4) when all of these values
are positive.

Claim: if `b` is positive in some chart `(p, q, r)`, then `c_S(b) != 0` for every
boundary divisor `D_S`. The same holds for `-b`. So the union over all `N(N-1)(N-2)`
charts of the Kohno–Pajitnov cones, together with their negatives, lies in the
region `{all c_S != 0}`, where
`pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3` already gives
`Sigma^{n-3}`. The decones of the braid arrangement are among these charts. The
braid arrangement itself is not essential, and positivity on it forces
`sum a_ij > 0`, which is off the zero-sum locus.

Consequence: the tool "Kohno–Pajitnov circle-valued Morse theory in other charts"
(`research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md`, Section E.2)
cannot prove any case of `pure-braid-nonresonant-zero-twist-characters-in-sigma`,
in any degree. The same goes for any method whose input is positivity on the
meridians of a standard chart.

Proof.

1. Adding the row relations over `x ∈ T` gives
   `2 sum_{pairs in T} b + sum_{x in T} b_xr = 0`. Row `r` gives
   `sum_{x in T} b_xr = 0`. Hence `sum_{pairs in T} b = 0`.
2. By positivity, `b_pq = - sum_{pairs in T, != {p,q}} b < 0`. Since `|T| = n >= 3`,
   the sum is over at least two pairs.
3. Let `D_S` be a boundary divisor. Replacing `S` by `S^c` if needed, `r ∉ S`, so
   `S ⊊ T`, because `|S| <= N - 2 = |T| - 1`.
   - If `{p, q} ⊄ S`, then `c_S` is a nonempty sum of positive meridian values,
     so `c_S > 0`.
   - If `{p, q} ⊆ S`, then by step 1, `c_S = - sum_{pairs in T not in S} b`. That
     sum is nonempty, because `S ⊊ T`: pair any `t ∈ T \ S` with `p`. It avoids
     `{p, q}`, so every term is positive and `c_S < 0`.
4. Negating `b` negates every `c_S`. The identity `c_S = c_{S^c}` used in step 3
   comes from adding the row relations over `S` and over `S^c`:
   `2 c_S + e(S, S^c) = 0 = 2 c_{S^c} + e(S, S^c)`, where `e(S, S^c)` is the sum
   over pairs that meet both. ∎

Step 2 is Kohno–Pajitnov's own sign condition. The hyperplane at infinity of the
chart is the divisor `D_pq`, and its meridian value `b_pq` is minus the sum of
all the finite meridian values. The obstruction says that every other boundary
divisor inherits a definite sign, as well.

Status: UNREVIEWED (swarm-0917 worker w20-z-last1, 2026-09-17). The proof is
elementary and complete as written. The citation of Kohno–Pajitnov Theorem 2.4
(positive classes, essential arrangements) is taken from the 2026-09-13 artifact,
Section B.3; the obstruction itself uses only the definition of positivity.
