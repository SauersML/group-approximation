---
rg: 2
id: b7-finite-two-cell-firewall-proof
kind: route
title: Restrict finite quotients of a two-cell group to the canonical B7 corner
target: b7-faithful-two-cell-retains-or3-prefix-defect
requires:
  - canonical-b7-or3-corner-defeats-finite-prefix-actors
  - full-support-factor-refutes-exact-exhaustive-typed-cap-chain
---

For each sufficiently large `n`, identify `K` with its image in `F_n` and
decompose `F_n` into right cosets `Kf`.  Each such coset is
invariant under left multiplication by `K` and carries one regular
`K`-module.  Hence `Res^(F_n)_K l2(F_n)` is `[F_n:K]` copies of `l2(K)`, proving
`(BTF2)` after normalized traces are taken.

The operators `X^*X`, `P`, `D`, and the rational central idempotent `p_rho`
all belong to the displayed copy of `C[K]`.  Their identity coefficients,
and therefore their normalized traces, are unchanged on passing from `K`
to `F_n`.  Insert the already checked B7 values `(BPC5)` to get `(BTF3)`.
Every defining relator evaluates to the identity in `F_n`, so the right side
of `(BTF4)` is zero while its left side is `1/92160`.

Choose the finite quotients diagonally so the kernel avoids the first `n`
nonidentity elements of `Pi` as well as every nonidentity element of the
finite subgroup `K`.  Their regular characters then converge pointwise to
the canonical character of `Pi`.  Thus the exact quotient models are
canonical microstates, not merely isolated finite evaluations.

For the concrete cell `(BTF6)`, the artifact computes with exact rational
matrices.  On `<e_0,e_4>`, `R_2` is the coordinate swap and both `A` and
`B` restrict to `diag(-1,1)`.  Their group commutator is therefore `-I` on
that plane and `I` off it, namely `(BTF7)`.  The additive commutator has two
orientations; left compression by `q_3` and right compression by `q_1P`
keeps only `|e_4><e_0|`, proving `(BTF8)`.

Finally, the raw-prefix telescope identifies `(BTF9)` as exactly the
vanishing of `(BTF8)` once incidence and source-boundary terms are paid.
The exhaustive typed-chain firewall rules out imposing that oriented row
universally over the full Fano frame while retaining the supplied marked
full-support factor.  This proves both sides of the stated finite-two-cell
dichotomy.
