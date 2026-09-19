---
rg: 2
id: mod-s2-maslov-line-is-optimal-for-torelli-characters
kind: claim
title: No character of a finite-index subgroup of Mod(S_2) containing Torelli beats the metaplectic Maslov line at the cube root, so the Torelli-abelian gap is exactly 1/(15m)
distinct_from:
  mod-s2-torelli-characters-have-a-metaplectic-maslov-line: that proves the upper bound d(H) <= 1/(15m) and the reduction to small positive characters; this is the matching lower bound, which is open.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that asks for a gap over all exact representations; this is the Torelli-abelian monomial subclass only, and it predicts the exact constant 2 sin(pi/30).
---

**OPEN.** Notation of `mod-s2-torelli-characters-have-a-metaplectic-maslov-line`. For every finite-index
`Gamma' <= Sp_4(Z)`, with `H = pi^-1(Gamma')`,

```text
d(H)  =  1/(15 m(Gamma')).                                                  (C)
```

Equivalently, by (ML5) of that claim, `H` has no *small positive character*: no `psi : H -> R/Z` with
`psi(t_o)` in `(0, 2/(15m))` for every `H`-class `o` of separating twists.

**Weak form (C_cof).** (C) holds on a cofinal family of congruence subgroups. That already gives
`d_inf = inf_N d(Gamma(N)) = 1/30`. So it proves the bus hole `mod-s2-torelli-abelian-census-limit-is-positive`
(w11-pull), with the exact value.

**Evidence.**
- The w11 census gives `d` in `{1/15, 1/30}` on 29 subgroups, which is exactly `1/(15m)`.
- (ML4): the continuous directions are excluded. No real character of `H` is positive on all separating twists.

**How it can fail.**
- A single `H` carrying a small positive torsion character refutes (C). It then gives a monomial representation with
  `||rho(t_s) - omega||_op < 2 sin(pi/(15m))`.
- Such a `psi` has to be nontrivial on `K` and off the Maslov line. On the transfer vector `ell_T` it must satisfy
  `5 sum_i psi(t_(o_i))` in `Z_(>0)`, which only needs `[M:H] >= 3m/2`. So the transfer alone does not exclude it.
- A family `H_j` with `d(H_j) -> 0` would refute (C_cof). Its monomial representations `Ind theta_j` are exact
  and satisfy `||rho_j(t_s) - omega||_op -> 0`. So it would also refute
  `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`, and with it the flagship
  `deligne-triple-cover-exact-mf-radical`.

**How it can be proved on one H.** Exhibit a nonnegative `ell` in the relation lattice `L(H)` with `F(ell) = 5m`: a
product of exactly `5m` separating twists, each lying in `H`, that is a product of commutators in `H`. This is a
separating-only Lefschetz-type relation of Maslov number `m`, with monodromy in `H`. For `H = M` this is `t_s^5`.

## Attempts

- **2026-09-18, swarm-0917-w12-w12-deligne-break (cohomology-index): posed.** Averaging and transfer arguments give
  only `d(H) >= 1/(15[M:H])`, and nothing when `3 | [M:H]`.
  - Relations whose monodromy has finite image `Phi` in `Sp_4(Z)` have `F = 0`. The preimage `Phi~` in `Gamma~` is
    central-by-finite, so `[Phi~, Phi~]` is finite (Schur), and it meets the torsion-free `<z>` trivially. Then (ML1)
    gives `n = 0`. So they contribute no certificate.
  - A certificate therefore needs a relation whose monodromy has infinite image.
