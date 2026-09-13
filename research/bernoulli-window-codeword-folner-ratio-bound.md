---
rg: 2
id: bernoulli-window-codeword-folner-ratio-bound
kind: claim
title: A Bernoulli window configuration has value at least log q divided by the right Følner ratio of its codeword set
distinct_from:
  bernoulli-witness-information-is-bounded-by-code-reads: that divides log q by the number m of codewords reading the site; this divides by inf_S |SF|/|S|, which is 1 whenever <F F^-1> is amenable, however large m is.
  bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup: that constrains the difference subgroup <E E^-1> of the window; this constrains the codeword group <F F^-1>.
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
**ESTABLISHED** (artifact Section 5, route `bernoulli-window-folner-ratio-bound-proof`). Verification has been requested from `w4-vf-positive-b`.

Let `G` be a countable group, `(k, E, F, psi)` a configuration, and `x` iid uniform on `(A^k)^G` with `|A| = q`. Then

    k log q <= lambda(F) H(psi(x|_E)) + H( x(1) | y_F ),     lambda(F) = inf_(S finite nonempty) |S F| / |S| ,

so `Phi >= log q / lambda(F)`. Moreover `lambda(F) = 1` exactly when `<F F^-1>` is amenable, and then `Phi >= log q`.

**Consequences.**
* With the read-degree bound, `Phi >= log q / min{m, lambda(F)}`.
* A deficit witness needs a nonamenable codeword group.
* A family with `Phi -> 0` needs `lambda(F) -> infinity`.

This is the Rokhlin form of the count `|F| log |A| <= |FN| H(y(e))` behind the amenable case of `injective-ca-random-order-transport-is-dominated`. Its only group-dependent step is the choice of a set `S` with ratio near `1` (artifact Section 7).
