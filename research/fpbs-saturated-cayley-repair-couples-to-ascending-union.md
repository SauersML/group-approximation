---
rg: 2
id: fpbs-saturated-cayley-repair-couples-to-ascending-union
kind: claim
title: The relative Cayley cost of a line is sandwiched by one-letter repair costs, and a letter-saturated certificate at a malnormal letter subgroup gives cost 2 for the Bernoulli shift of the ascending union it generates, so for ccdcDD it refutes the Gamma_mal floor
artifacts:
  - research/artifacts/fpbs-relative-cayley-cost-letter-saturation-2026-09-18.md
  - experiments/fpbs-relative-cayley-cost-2026-09-17/malnormal_check.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/probe.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/aut_orbit.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/census_usage.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/witnesses.py
distinct_from:
  fpbs-letter-contact-words-have-relative-cayley-cost-one: that proves RC(v) = 1 when a letter subgroup has a contact; this handles the no-contact words, by bounding RC between one-letter repair costs and coupling those to finite cost of ascending unions
  fpbs-relative-fixed-price-free-pairs: that is the open inequality relC(R_L; R_K) <= (rk L - rk K)^+ with unrestricted repair labels; this is about repairs restricted to one Cayley letter (equivalently labels in H t^{+-1} H), which dominate relC and imply that inequality at the pair (F_2, <c,v>)
  fpbs-mal-bernoulli-single-stage-floor: that is the open floor for Gamma_mal; this shows the c-saturated route to RC(ccdcDD) = 1 would refute it, and runs the same shift argument for every ascending union Gamma_v
  fpbs-malnormal-coset-cycles-linear-perimeter: that floors packing certificates across malnormal pairs; this identifies one-letter repair costs as such a pair problem, so the floor applies to letter-saturated certificates
  fpbs-locally-free-malnormally-exhausted-finite-cost: that is the open finite-cost statement for malnormally exhausted locally free groups; this shows a c-saturated certificate for RC(v) = 1 at a malnormal <c,v> would prove it for the Bernoulli shift of Gamma_v
---

**ESTABLISHED (written deduction).** Proof in `fpbs-saturated-cayley-repair-couples-to-ascending-union-proof`.

**Setting.**
- `a` is a free p.m.p. action of `F(c,d)` with `R = E_a`, and `v` is not in `<c> cup <d>`.
- `RC(v)` is as in `fpbs-letter-contact-words-have-relative-cayley-cost-one`.
- `H_s = <s, v>`.
- `rho_t(H) = inf { mu(E) : E subset Phi_t, <R_H cup E> = R }`.

**Proposition B (sandwich).**

```text
max(1, rho_d(H_c) + rho_c(H_d))  <=  RC(v)  <=  1 + min(rho_d(H_c), rho_c(H_d)).
```

The `s`-saturated family `{Phi_s cup E : E subset Phi_t}` has value exactly `1 + rho_t(H_s)`.

**Lemma 4.1 (sliding).** `rho_t(H)` is the relative cost of `R` over `R_H` with labels restricted to
`H t H cup H t^{-1} H`. So `rho_t(H) >= relC(R; R_H)`.

**Corollary C (coupling).** Let `Gamma_v` be the direct limit of `F_2` along `c -> c, d -> v`, and `beta_v` its
Bernoulli shift. If `rho_d(<c, v>) = 0` for the Bernoulli shift of `F(c,d)`, then `C(beta_v) = 2`.
- For `v0 = ccdcDD`, `<c, v0> = <c, dcDD>` is the stage pair of `Gamma_mal`. So `rho_d(<c, dcDD>) = 0` on Bernoulli
  refutes `fpbs-mal-bernoulli-single-stage-floor`.
- Conversely, if that floor holds, the `c`-saturated family for `v0` has value `1 + rho_d > 1`.
- If `<c, v>` is malnormal, `Gamma_v` is malnormally exhausted. A `c`-saturated certificate for `RC(v) = 1` would then
  prove `fpbs-locally-free-malnormally-exhausted-finite-cost` for `beta_v`.

**Class kill: letter-saturated contact repair.**
- *Class.* `F = Phi_s cup Phi_t|_M` with `M` a complete section of the relation of a subgroup of
  `I = H_s cap t^{-1} H_s t`.
- *Invariant.* `rank(I)`.
- *Step where it dies.* The small complete section: when `I = 1` the only complete section is `X`, so the family
  costs 2.
- *Why nothing is left to thin.* By Lemma 6.1 of the artifact, adjacent `H_s`-classes are joined by exactly `|I|`
  forward `t`-edges.
- *What remains.* By Lemma 6.2, the class graph still has cycles. So what remains is cycle deletion across a malnormal
  pair, where packing certificates are floored by `fpbs-malnormal-coset-cycles-linear-perimeter`.
- *Words killed.*
  - The sharp-test word `cdcDcd`: both letters, both malnormal.
  - `ccdcDD`: both letters.
  - 1484 of the 1539 classes of length at most 9 in which each letter is used at least 3 times.

**Not ruled out.** Mixed families, which use `c`-edges to create cycles in the `d`-class graph and conversely. The
lower bound `rho_d(H_c) + rho_c(H_d)` may lie below `1`. `RC(cdcDcd)` stays OPEN.
