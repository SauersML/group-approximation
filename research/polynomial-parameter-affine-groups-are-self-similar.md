---
rg: 2
id: polynomial-parameter-affine-groups-are-self-similar
kind: claim
title: Affine groups over Z[1/m][t_1..t_k] act self-similarly through parameter coordinates
distinct_from:
  principal-ideal-affine-groups-are-self-similar: that is Zaremsky's criterion, which needs a finite-index principal ideal xR with ∩ x^k R = 0 and acts on the digit tree of R^n; this acts on Z_p^n x Z_p^k by evaluating polynomial entries at a parameter coordinate, so R = Z[1/m][t_1..t_k] qualifies although it has no such ideal.
  affine-self-similar-coordinate-rings-are-one-dimensional: that obstructs digit self-similar affine maps x -> Mx + b with constant M and b over a section-closed subring of O; here the linear part varies with the parameter, the states use the substitutions t_j -> a_j + p t_j, and no section-closed subring of Z_p is needed.
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`polynomial-parameter-affine-groups-are-self-similar-proof`. ~~Not independently
reviewed.~~ *Reviewed (lane `bh-poly-linear-review`, 2026-09-12):* the state formula,
the divisibility by `p` in `R^n`, faithfulness and Zaremsky's definition were
checked, and no correction was needed.

**Setting.**
- Let `m >= 1`, `k >= 0`, `R = Z[1/m][t_1,...,t_k]` and `n >= 1`.
- Let `Γ = E_n(R)` or `Γ = SL_n(R)`.
- Let `p` be a prime not dividing `m`, so `Z[1/m] ⊂ Z_p`.

**Claim.** `R^n x| Γ` acts faithfully on `X = Z_p^n x Z_p^k` by

```text
(g,b) · (v,s) = (g(s) v + b(s), s).
```

This action preserves the rooted `p^(n+k)`-regular tree of residues mod `p^j`,
and it is self-similar: every first-level state lies in `R^n x| Γ`.

**The states.**
- Fix a first-level vertex `(e,a)` with `e in {0..p-1}^n` and `a in {0..p-1}^k`.
- Let `σ_a` be the ring endomorphism `t_j -> a_j + p t_j` of `R`.
- Let `c` be the digit of `g(a)e + b(a)`.

Then `(g,b)` sends `(e,a)` to `(c,a)`, and its state there is

```text
( σ_a(g), (σ_a(g) e + σ_a(b) - c) / p ).
```

For `k = 0` this is Zaremsky's action with `J = pZ[1/m]`
(`principal-ideal-affine-groups-are-self-similar`). For `k >= 1` it is the input
that `polynomial-linear-groups-satisfy-boone-higman` uses.
