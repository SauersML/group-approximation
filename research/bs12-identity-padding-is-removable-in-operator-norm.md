---
rg: 2
id: bs12-identity-padding-is-removable-in-operator-norm
kind: claim
title: Identity padding can always be removed from operator-norm BS(1,2) correction, so trivially padded correction is exactly same-dimension matricial stability of BS(1,2)
artifacts:
  - experiments/bs12-site-removal-2026-09-17/run_excision.py
  - experiments/bs12-site-removal-2026-09-17/run_excision.txt
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open padded correction statement (TPC); this proves that its padding is worthless, so (TPC) is equivalent to the open unpadded question and is not a weaker target.
  higman-seam-gate-needs-only-padded-bs-correction: that shows the Higman gate needs only identity-padded rather than same-dimension correction; this shows the two are the same statement, so the gate's BS(1,2) half is exactly Eilers--Shulman--Sorensen Question 3 for BS(1,2).
  bs1n-rq-padded-opnorm-stability: that is Willett's theorem with an uncontrolled finite-quotient auxiliary; this removes only auxiliaries on which both generators act trivially, and is proved from scratch.
  higman-exact-packet-cycles-collapse-opnorm: that is the glued-cycle collapse (CGC) for exact packets; this concerns a single exact packet and its almost-invariant vectors.
---

**ESTABLISHED** by `bs12-identity-padding-is-removable-in-operator-norm-proof`.
This is an elementary written proof, not Lean-verified. The numerics are a sanity
check only.

All norms are operator norms. An *exact packet* is a pair of unitaries `(C,Z)` with
`C Z C^* = Z^2`.

**Theorem (padding removal).** Let `0 < eps <= 4^(-8)`, and put
`m = floor(log_4(1/eps)/4)`, so `m >= 2`. Let `A, B` be any unitaries in `U(n)`,
with no assumption on `||A B A^* - B^2||`. Suppose some exact packet `(C,Z)` in `U(n+k)` satisfies

```text
||C - (A (+) 1_k)|| <= eps,     ||Z - (B (+) 1_k)|| <= eps.                 (P)
```

Then there is an exact packet `(C_0,Z_0)` in `U(n)` with

```text
||C_0 - A|| <= 3 pi/(2m-1) + 3 eps + 24 eps^(5/8),
||Z_0 - B|| <= 3 pi 2^(-m) + eps + 12 eps^(5/8).                          (R)
```

Both bounds are `O(1/log(1/eps))`, uniformly in `n` and `k`.

**Corollary (TPC is ESS Q3).** The trivially padded correction statement `(TPC)` of
`bs12-trivially-padded-opnorm-correction` holds if and only if `BS(1,2)` is matricially
stable in operator norm with the dimension held fixed. That is: for every `eps>0` there is
`delta>0` such that every pair in `U(n)` with `||A B A^* - B^2|| <= delta` is
`eps`-close to an exact packet in `U(n)`. The fixed-dimension statement is the case
`n = 1, m = 2` of Eilers--Shulman--Sorensen arXiv:1808.06793v4, Section 6,
Question 3, which the authors leave open: "We do not at present have any tools to
address this case." (quoted in `bs1n-rq-padded-opnorm-stability-citation`).
- *Only if:* compose the `(TPC)` modulus with `(R)`.
- *If:* take `k = 0`.

## What the proof does

1. *Normal form.* An exact packet splits orthogonally into `F = ker(Z-1)`, on which
   `C` is an arbitrary unitary, and cyclic blocks. On a cyclic block, `Z` is diagonal
   along the squaring orbit of an odd-order root of unity `exp(2 pi i theta)`, and `C`
   shifts the orbit. Site `j` of a block carries the binary reading of
   `2^j theta`. The *depth* of a site is the length of the constant initial block of
   its reading, and `|lambda_j - 1| >= 4^(-(depth-1)/2)`.
2. *Run excision.* In every 0-run or 1-run of length `z >= s+4r+1` of the periodic
   word, cut a deep segment of length `p = z-s-2r` into its own cycle, with `Z = 1` on
   that cycle.
   - *The remaining cycle.* It is the orbit of the word with those `p` digits deleted,
     and its eigenvalues move by at most `pi 2^(-s)`.
   - *The change of `C`.* It is a swap of two edge targets. Pair the sites
     `c+i <-> c+p+i` for `-r <= i < r`, and spread the swap `sigma = u^(2r-1)` over the
     `2r-1` pair edges by a gauge `W`.
   - *The result.* The conjugate `(C_1,Z_1)` is an exact packet with
     `||C_1-C|| <= pi/(2r-1)` and `||Z_1-Z|| <= 3 pi 2^(-s)`.
3. *Energy leak.* The energy form `E(y) = ||(C-1)y||^2 + ||(Z-1)y||^2` is block diagonal.
   On every block, every vector satisfies
   `||(1-P_(ker(Z_1-1))) y||^2 <= a E(y)`, with `a = 4^(s+2r-1) + (2r+1)^2`.
   - *Shallow sites.* The potential `|lambda-1|^2` controls them.
   - *Short runs and the deep ends of long runs.* Telescoping from the depth-1
     neighbour controls these.
   - *Everything else.* It lies in the new fixed space.

   Since `E(x) <= 2 eps^2` on the padding space `V`, the space `V` lies within
   `sqrt(2a) eps` of `ker(Z_1-1)`.
4. *Split off and rotate.* Inside the new fixed space, make the projection of `V`
   exactly reducing and trivial at cost `O(eps + 1/r + sqrt(a) eps)`. Then rotate it onto
   `V` and restrict to `V^perp`. Take `r = s = m`.

## Consequences

- **The padding class is killed.** No proof strategy for `(TPC)` can gain anything from
  identity padding. Every such proof is a proof of the unpadded ESS question for
  `BS(1,2)`.
  - *Invariant:* the almost-invariant vectors of the correcting packet.
  - *Where it dies:* step 3. Every almost-invariant vector of an exact packet lies near
    the fixed space of a nearby exact packet, because low-energy vectors live on deep
    binary runs, and deep runs can be excised at cost `1/r`.
- **The Higman route is gated by a published open problem.** By
  `higman-seam-gate-needs-only-padded-bs-correction`, the marked Higman collapse
  `(HMF5)` follows from `(TPC)` plus `(CGC)`. By this claim, that is the same as
  ESS Question 3 for `BS(1,2)` plus `(CGC)`.
- **This supersedes the earlier partial removals.** Earlier waves removed padding only
  in special cases, such as spectral gaps or localized padding vectors. The residual
  configuration there was long cycles with Dirichlet-type low-energy states on long
  binary runs. That is exactly what run excision removes. The cost is a modulus
  `O(1/log(1/eps))` instead of `O(sqrt eps)`.
- **The rate is only a byproduct.** The logarithmic rate comes from spreading an
  order-two holonomy over `2r` edges, while keeping those edges at depth at most
  `s+2r`, where the potential is `4^(-(s+2r))`. This is not claimed to be sharp.

## Numerical check (evidence only)

`run_excision.py` builds the construction of step 2 on explicit words and runs the whole
pipeline of step 4 with `V` spanned by the lowest eigenvectors of `E`. The results are in
`run_excision.txt`.
There are five cases, on words of length `59`, `225` and `134`, with one or two long
runs, `mu` in `{1, -1, i, 0.6+0.8i}` and `k` from `1` to `3`.
- `(C_1,Z_1)` is exact to `5e-15` in all five cases.
- `||C_1-C||` is within `1%` of the bound `pi/(2r-1)` in every case.
- `||Z_1-Z||` is at most `3.5e-3`, well inside `3 pi 2^(-s)`.
- The observed leak ratio `||(1-P_(F_1))y||^2/E(y)`, over the six lowest
  eigenvectors of `E`, is at most `160`, far below `a`.
- In four cases the whole of step 4 runs. The output `(C_0,Z_0)` is exact and unitary
  to `1.4e-14`, and `||C_0-A||` exceeds `||C_1-C||` by at most `0.005`.
- In the fifth case (`r=16`, `k=3`), `theta = 0.57 > 1/2`. That case is outside the
  theorem's regime, and the script skips it.
