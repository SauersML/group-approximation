---
rg: 2
id: z7-rips-contractible-at-scales-11-13-15-17
kind: claim
title: The Rips complex of Z^7 in the l^1 metric is contractible at scales 11, 13, 15 and 17
distinct_from:
  z7-rips-contractible-at-scale-10: that is scale 10, closed by a 1.4 MB point-level certificate with K (cone-collapse) moves; this is scales 11, 13, 15, 17, closed by orbit-level certificates with domination moves only
  z7-rips-contractible-at-scales-12-14-16-and-18-to-54: that is a partition criterion that excludes r = 11, 13, 15, 17 because some unbalanced partition of r has fewer than 7 parts; this handles those four scales by layered orbit certificates
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1); this is four single scales for n = 7
---

`VR(Z^7, d_1; r)` is contractible for `r = 11, 13, 15, 17`. A finite set spans a simplex iff its `l^1` diameter is at
most `r`.

Context. These are the last scales left open for `n = 7` in Zaremsky's conjecture
(`zn-rips-contractible-at-every-scale-r-ge-n`), once `z7-rips-contractible-at-scale-10` is in. With them, `n = 7` holds
at every `r ≥ 7`.

Proof: route `z7-rips-contractible-at-scales-11-13-15-17-proof`. It uses the lifted reduction of
`z7-rips-contractible-at-scale-10-proof` (§1–§3, valid for every `(n, r)`): it is enough to give, for each
`k = 2, …, 7`, a certificate of (D) moves on `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }` that ends at `{e_k}`.

The new ingredient is an **orbit move**. Let `T_j` be the points whose last nonzero coordinate is `j`, and let `H_j` be
the signed permutations of the coordinates before `j`. If every `C ∩ T_i` is `H_i`-invariant, a single dominator `w`
for `x ∈ T_j` that works against the enlarged set `H_j · C` deletes the whole orbit `H_j x`. Each deletion keeps the
invariance, so the certificates list one line per orbit.

For all 24 pairs `(k, r)` the certificates are short: 8,301 lines at `(7, 17)` stand for 6,863,494 point moves, and
all 24 files together take 296 KB compressed. An independent verifier expands every orbit, checks every hypothesis of
the orbit move exhaustively, and confirms `{e_k}` at the end. The slowest replay, `(7, 17)`, explores `9.3·10^9`
search nodes in about 3 minutes.
