---
rg: 2
id: bs12-images-in-nv-have-logarithmic-table-length
kind: claim
title: If f g f^-1 = g^l in a Brin--Thompson group nV with |l| ≥ 2, the table lengths and exponent sums of g^N grow at most logarithmically in N
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that proves zero periodic exponents, open periodic sets and the bound c(1 + log|N|)^2 on exponent sums; this bounds whole table lengths, and so exponent sums, by c(1 + log|N|).
  bs12-embeds-in-brin-thompson-2v: that is the open embedding question; this is a necessary condition on any witness.
---

**ESTABLISHED** through `bs12-logarithmic-table-length-proof` (elementary; no
novelty claimed).

**Setting.** As in
`bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`:
- `nV` acts on `C^n` by tables of bricks with prefix replacement;
- `L(h)` is the largest side length in a table of `h`, minimized over tables,
  with `L(id) = 0`;
- `δ_h(x) ∈ Z^n` is the exponent vector of `h` at `x`, i.e. `(|v_j| - |u_j|)_j`
  on a table brick containing `x`.

**Statement.** Let `g, f ∈ nV` and `l ∈ Z` with `|l| ≥ 2` and `f g f^-1 = g^l`.
Then there is `c > 0` such that, for every `N ≠ 0` and every `x ∈ C^n`,
- `L(g^N) ≤ c (1 + log_2 |N|)`, and
- `|δ_{g^N}(x)|_∞ ≤ c (1 + log_2 |N|)`.

**Consequence.** For `BS(1,2) = <s, u | u s u^-1 = s^2>` and any homomorphism
into `nV`, the image of `s^N` has a table with all sides of length
`O(log |N|)`. So `s^N` rewrites only prefixes of length `O(log |N|)` in each
coordinate.

For comparison, Callard--Salo (arXiv:2208.00685v3, §1, the paragraph after
their main theorem) note that the radius of the n-th power of their distorted
automorphism of the full shift is `Θ(log n)`. Their distortion element in `mV`
(§6.3) comes from the same SMART machine. The bound rules out any witness whose
table lengths grow faster than logarithmically, including linear growth from
attracting periodic points.
