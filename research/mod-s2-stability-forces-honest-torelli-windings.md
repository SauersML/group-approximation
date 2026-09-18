---
rg: 2
id: mod-s2-stability-forces-honest-torelli-windings
kind: claim
title: Point-norm stability of Mod(S_2) would make honest representations carry Dadarlat's Sp4 windings on a separating twist that is operator-norm close to the identity
distinct_from:
  mod-s2-is-point-norm-matricially-stable: that is the open stability statement; this is an unconditional implication from it to a statement about honest representations only.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that concerns honest representations with the separating twist near a primitive cube-root scalar; this concerns honest representations with the separating twist near the identity, where no scalar obstruction exists, and measures the trace-log winding.
  dadarlat-linear-groups-have-nonzero-h2-windings: that produces asymptotic homomorphisms of Sp_4(Z) with nonzero winding; this transports them, under stability, to honest representations of Mod(S_2).
  sp4-quasirep-windings-budget-and-saturation: that bounds normalized windings of Sp_4(Z) quasi-representations; this computes the winding of the quasi-representation induced by an honest Mod(S_2) representation as a multiple of one trace-log.
---

**ESTABLISHED** through `mod-s2-stability-forces-honest-torelli-windings-proof`. Unreviewed; no novelty claimed.

**Notation.** `M = Mod(S_2)`, `pi : M -> Gamma = Sp_4(Z)`, `K = ker pi` (Torelli), `t_s` a separating
twist, `sigma : K -> Z` the separating-twist exponent count and `r = a/10` (`3 not | a`) as in (U1) of
`mod-s2-real-untwisting-identifies-deligne-norm-parameters`. For a unitary `A` with `||A - 1|| < 2` put

```text
kappa(A) = (1/2 pi i) Tr log A      (principal branch; a real number, exp(2 pi i kappa(A)) = det A).
```

**Statement.**

1. **(TW1) Honest windings are one trace-log.** Fix the relator `R = prod_{i<=g}[a_i, b_i]` of
   `sp4-quasirep-windings-budget-and-saturation` (`prod [a_i^, b_i^] = zeta^k`, `k != 0`), lifts
   `a_i~, b_i~ in M`, and `w = prod [a_i~, b_i~] in K`. Then `sigma(w) = -k/r = -10k/a != 0`, and there is
   `L` (depending only on these choices) such that every honest unitary representation `rho : M -> U(d)` with
   `L ||rho(t_s) - 1|| < 2` satisfies
   ```text
   kappa( prod [rho(a_i~), rho(b_i~)] ) = sigma(w) * kappa(rho(t_s)).
   ```
   Moreover `kappa(rho(t_s))` lies in `(1/10)Z`, since `det o rho` is a character of `M` and `H_1(M;Z) = Z/10`.
2. **(TW2) Stability transports Dadarlat windings.** If `M` is point-norm matricially stable (the full form
   in `mod-s2-is-point-norm-matricially-stable`), then there are honest representations
   `rho_n : M -> U(d_n)` with
   ```text
   || rho_n(t_s) - 1 ||_op -> 0     and     kappa(rho_n(t_s)) = -a kappa_n / (10 k) != 0 ,
   ```
   where `kappa_n != 0` is the integer winding of a Dadarlat asymptotic homomorphism of `Gamma` on `R`. In
   particular `|kappa(rho_n(t_s))| >= 1/(10|k|)` for all large `n`, while every eigenvalue of `rho_n(t_s)` tends
   to `1` uniformly.
3. **(TW3) Contrapositive.** If `mod-s2-near-identity-torelli-windings-vanish` holds, then `M` is not
   point-norm matricially stable. This is route `mod-s2-instability-via-vanishing-torelli-windings`.

**Reading.**
- The genus-two gate route (`deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability`) needs the
  full stability statement, so it needs honest `M`-representations that are *maximally flexible near the
  identity*: a separating twist whose whole spectrum converges to `1` while its eigen-angles still add up to
  a fixed nonzero fraction of `2 pi`. The same route also needs honest representations to be *rigid near
  `omega`* (`mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`). Both are statements about
  honest representations with infinite image, and they pull in opposite directions.
- The Dadarlat winding does not disappear on `M` because `H_2(M;Q) = 0`. It moves from the relators of
  `Gamma` onto the Torelli generator: stability can only hold if honest representations absorb it there.
