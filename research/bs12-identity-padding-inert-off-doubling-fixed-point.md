---
rg: 2
id: bs12-identity-padding-inert-off-doubling-fixed-point
kind: claim
artifacts:
  - experiments/bs12-padding-2026-09-17/kappa_cycle_bound.py
title: Identity padding in BS(1,2) operator-norm correction can be removed unless the correcting exact representation has almost-invariant vectors off the fixed space of b, which forces irreducible constituents of dimension at least 1/kappa
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open padded correction statement (TPC) itself; this proves that its padding can be stripped off at no essential cost in two uniform regimes, and names the only configuration in which padding can buy anything.
  higman-seam-gate-needs-only-padded-bs-correction: that shows the Higman gate needs only identity-padded correction rather than same-dimension correction; this shows identity padding is itself same-dimension correction except through long b-fixed-point-free constituents with almost-invariant vectors.
  bs1n-rq-padded-opnorm-stability: that is Willett's theorem with an uncontrolled finite-quotient auxiliary; this concerns only auxiliaries on which b acts trivially and is proved from scratch.
---

**ESTABLISHED (written elementary proof, not Lean-verified).**

All norms are operator norms. Write `M = A (+) 1_k` and `N = B (+) 1_k` on `C^n (+) C^k`, and let `V = 0 (+) C^k` be the padding space. Suppose `(C,Z)` in `U(n+k)` is an exact packet, `C Z C^* = Z^2`, with

```text
||C - M|| <= eps,     ||Z - N|| <= eps.                                  (P)
```

Call this an `eps`-padded correction of `(A,B)`. Nothing is assumed about `||A B A^* - B^2||`.

1. **Gapped removal.** Suppose `spec(B)` misses the open disc `D(1,gamma)`, and `eps < gamma/8`. Then there is an exact packet `(C_0,Z_0)` in `U(n)` with
   `||C_0 - A||, ||Z_0 - B|| <= eps (1 + 16/gamma)`.
   The same holds, with the same proof, when the padding block `1_k` of `M` is replaced by an arbitrary unitary `U` in `U(k)`; that is, for padding by any representation on which `b` acts trivially.

2. **Localization of the padding gain.** Let `F = ker(Z-1)`. It is reducing for `(C,Z)`. Let `G = F^perp`, with
   `kappa = inf { (||Cx-x||^2 + ||Zx-x||^2)^(1/2) : x in G, ||x|| = 1 }`.
   Suppose `kappa > 0`, and put `d = sqrt(2) eps/kappa + sqrt(eps)` with `d < 1/2`. Then there is an exact packet `(C_0,Z_0)` in `U(n)` with
   `||C_0 - A|| <= eps + sqrt(eps) + 8d`,     `||Z_0 - B|| <= eps + 8d`.
   In particular, if `kappa >= sqrt(eps)` and `eps <= 1/64`, both errors are at most `22 sqrt(eps)`.

3. **Long constituents are forced.** `kappa` is the minimum of the same quantity over the irreducible constituents of `(C,Z)|G`. An irreducible exact packet with no nonzero `Z`-fixed vector and of dimension `L` has this constant at least `1/L`. Hence padding removal at cost `22 sqrt(eps)` fails only if the correcting packet has a `b`-fixed-point-free irreducible constituent of dimension greater than `1/sqrt(eps)` that carries a unit vector moved by less than `sqrt(eps)`.

## Consequences

- **TPC equals same-dimension correction on gapped pairs.** On the class of pairs whose `B` has a spectral gap `gamma` at `1`, `(TPC)` with modulus `eps -> delta(eps)` gives same-dimension correction with modulus `eps(1+16/gamma) -> delta(eps)`. On this class the padding in `bs12-trivially-padded-opnorm-correction` is worth nothing, so any strict gain of `(TPC)` over the open Eilers--Shulman--Sorensen question lives on pairs whose `B` has spectrum accumulating at `1`.
- **Named residual configuration.** Padding can help only through an exact packet with no `Z`-fixed vector but with `sqrt(eps)`-almost-invariant vectors. The irreducible packets are `rho(O,mu)`: `Z` is diagonal on a squaring cycle `O` of odd-order roots of unity, and `C` is a weighted cyclic shift along the cycle. Almost-invariant unit vectors force `|O| >= 1/kappa`. The order is sharp. For the orbit of `1/(2^L-1)` with `mu=1`, `kappa L` is `3.82, 3.50, 3.32, 3.23, 3.18` at `L = 8, 16, 32, 64, 128`, apparently tending to about `pi`. The minimizer is a Dirichlet-type ground state that vanishes near the far sites. This is a numerical observation only, from `experiments/bs12-padding-2026-09-17/kappa_cycle_bound.py` and an inline run. A far site `|lambda-1| >= sqrt(2)` carries mass at most `kappa^2/2`, so the mass is spread over long runs of the cycle near `1`, that is, over long binary 0-runs of the angle. The worked example of such a packet is the compression of the orbit of `1/(2^L-1)` recorded in the Attempts of `bs12-trivially-padded-opnorm-correction`.
- **Class killed.** Every correction method whose padding block has `b`-spectrum `gamma`-separated from `spec(B)` and on which `b` acts trivially is, up to the factor `1+16/gamma`, a same-dimension correction method. Such a method cannot prove `(TPC)` without also proving same-dimension correction on gapped pairs.
  - **Invariant:** the spectral projection of `Z` onto the closed disc `D[1,eps]`.
  - **Where it dies:** that projection is exactly squaring-invariant, hence equal to `ker(Z-1)`, hence reducing.

Proof: `bs12-identity-padding-inert-off-doubling-fixed-point-proof`.
