---
rg: 2
id: mod-s2-is-not-point-norm-matricially-stable
kind: claim
title: The genus-two mapping class group is not point-norm matricially stable
distinct_from:
  mod-s2-is-point-norm-matricially-stable: that is the positive statement used by the genus-two gate route; this is its negation, filed so that a route into it can be recorded.
  mod-s2-near-identity-torelli-windings-vanish: that is a statement about honest representations only; this is the resulting instability statement.
---

**OPEN.** There are unital maps `V_n : Mod(S_2) -> U(d_n)` with `||V_n(m)V_n(m') - V_n(mm')||_op -> 0`
for all fixed `m, m'` such that no honest representations `rho_n : Mod(S_2) -> U(d_n)` satisfy
`||V_n(m) - rho_n(m)||_op -> 0` for every fixed `m`.

**Route.** `mod-s2-instability-via-vanishing-torelli-windings`: the witnesses are `V_n = W_n o pi` for a
Dadarlat asymptotic homomorphism `W_n` of `Sp_4(Z)`, and the only open input is
`mod-s2-near-identity-torelli-windings-vanish`.

**Consequence if it holds.** `mod-s2-is-point-norm-matricially-stable` is false, and route
`deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability` is dead as filed. The gate would then need the
weaker form recorded in that node (stability only for maps sending `t_s` near `omega I`), which this
argument does not touch: the witnesses here send `t_s` to `1`.

## Attempts

- **2026-09-18, swarm-0917-w10-w10-deligne-last1: subgroup tests die; the winding lands on one twist.** Every test that reads
windings on a subgroup `L <= Mod(S_2)` sees classes pushed into `H_2(Mod(S_2);Z) = Z/2`. In particular a
Voiculescu-type pair on two commuting twists would need nonzero Bott index, which is the winding of the
torus class, and that class is torsion in `Mod(S_2)`. Inducing a winding from a finite-index subgroup `H`
sums it over `Mod(S_2)/H`, which is transfer after corestriction and factors through
`H_2(Mod(S_2);Q) = 0`. The Dadarlat winding survives only as the separating-twist trace-log of
`mod-s2-stability-forces-honest-torelli-windings`. These remarks use that the winding pairing is additive on
`H_2`, which Dadarlat proves but the graph has not imported verbatim; they are not filed as a claim.
