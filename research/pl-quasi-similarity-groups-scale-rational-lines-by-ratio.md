---
rg: 2
id: pl-quasi-similarity-groups-scale-rational-lines-by-ratio
kind: claim
title: In a periodic PL quasi-similarity group of the line, an element normalizing a copy of (Q,+) acts on it by multiplication by its own similarity ratio
distinct_from:
  lifts-add-no-unipotent-divisibility: that rules out central and covering lifts of groups without (Q,+); this covers groups such as <T-bar, x -> 2x>, which contain (Q,+) and BS(1,2) and have no such central series, and it pins the scaling factor instead of forbidding the line.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this is an obstruction for one host family, used in `fg-pl-quasi-similarity-groups-contain-no-gl-2-q`.
---

**ESTABLISHED** through `pl-quasi-similarity-groups-scale-rational-lines-by-ratio-proof`.
Not independently reviewed. The argument is elementary and no priority is claimed.

## Definition

A **periodic PL quasi-similarity group** is a group `Γ` of homeomorphisms of `R`
such that:

- **(P1) PL with non-divisible slopes.** Every element is piecewise linear with
  locally finitely many breakpoints. Its one-sided slopes lie in a subgroup `P` of
  `R^x` such that the only element of `P ∩ R_{>0}` that is a `k`-th power in
  `P ∩ R_{>0}` for every `k >= 1` is `1`. Any finitely generated `P`, for example
  `2^Z`, qualifies.
- **(P2) Quasi-similarity.** For every `γ in Γ` there is `c(γ) in R^x` with
  `sup_x |γ(x) - c(γ)x| < ∞`.
- **(P3) Periodicity.** Every orientation-preserving `γ` with `c(γ) = 1` commutes
  with some translation `x -> x + L`, `L > 0` (`L` may depend on `γ`).

`c : Γ -> R^x` is a homomorphism, the **similarity ratio**.

**Examples.**
- `T-bar`, the lifts of Thompson's `T`: `c = 1`, `L = 1`, `P = 2^Z`.
- `T-check = <T-bar, δ>` with `δ(x) = 2x`. Conjugation by `δ^-1` maps `T-bar`
  into itself, so `T-check` is an ascending HNN extension of the finitely
  presented `T-bar`, hence finitely presented. It contains `(Q,+)` (from `T-bar`)
  and `BS(1,2) = <x -> x+1, δ>`, with its exponentially distorted cyclic
  subgroup. So it passes the root's obstructions O1, O3 and O4.
- Adding `x -> -x`, the Stein-type lifts over `Z[1/m]` with dilations
  `x -> p x` (`p | m`), and all their subgroups.

## Statement

Let `Γ` be a periodic PL quasi-similarity group, let `D <= Γ` be a subgroup
isomorphic to `(Q,+)`, and let `t in Γ` normalize `D`. Then `t` acts on `D` by
multiplication by `c(t)`. In particular `c(t)` is rational, and the image of
`N_Γ(D) -> Aut(D) = Q^x` lies in `c(Γ) ∩ Q^x`.

## Consequences

- `fg-pl-quasi-similarity-groups-contain-no-gl-2-q`: if `Γ` is finitely generated,
  or just if `c(Γ) ∩ Q^x` involves finitely many primes, then `Γ` contains no copy of
  `Aff(Q)`, `B_2(Q)`, `SL_n(Q)`, `PSL_n(Q)`, `GL_n(Q)` or `PGL_n(Q)` (`n >= 2`).
  If `Γ` preserves orientation it contains no `Aff(Q)`, `B_2(Q)`, `GL_n(Q)` or
  `PGL_n(Q)` at all.
- **Where the line lives.** Every copy of `(Q,+)` in `Γ` consists of elements of
  ratio `1` without fixed points (Steps 0 and 4 of the proof). It is detected by
  translation number, as the `Q <= T-bar` of Belk--Hyde--Matucci is.
- **Not excluded.** `Q x|_2 Z <= T-check` (scaling by `2 = c(δ)`) is allowed. Whether
  `T-check` contains it is open.
