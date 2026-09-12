---
rg: 2
id: osin-horn-separator-is-opnorm-stable
kind: claim
title: Osin's finite separator has a dimension-free operator-norm modulus
distinct_from:
  matrix-restricted-burnside-gap: that asks for moduli for every restricted Burnside relator at every pair (m,N), which is a whole family of inequalities; this asks for ONE inequality attached to one fixed presentation and one fixed word set, and is a strictly smaller target.
  osin-torsion-universal-theory-separator: that is the classical group-theoretic separator, proved with no analysis and asserting nothing about matrices; this is the analytic upgrade that turns it into a statement about operator-norm models.
  finite-group-opnorm-support-profile: that corrects an approximate model of a fixed FINITE group to an exact representation of that group; here the hypothesis is a mixture of exact-looking relators and power tests, and there is no finite group to correct towards.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Take the data `G = <x_1..x_s | R_1..R_t>`, the exponent `n` and the words
`W_1,...,W_q` of `osin-torsion-universal-theory-separator`, and put
`delta_n = 2 sin(pi/n)`.

**Claim.**  There are `eta > 0` and finitely many words
`v_1,...,v_r in F_s` such that for every `d` and every
`U = (U_1,...,U_s) in U(d)^s`,

```text
|| R_i(U) - I || < eta              (1 <= i <= t),
|| v_l(U)^n - I || < eta            (1 <= l <= r),
```

together imply

```text
min_(1 <= j <= q) || W_j(U) - I || < delta_n / 2.                (OSM1)
```

The constants `eta`, the word list `v_1..v_r` and the bound are independent
of the matrix size `d`. Nothing else appears: no trace, no normalized
Hilbert--Schmidt norm, no rank, no corner, no selected support.

## Why this is the whole of the analytic content

`osin-torsion-universal-theory-separator` already gives the **exact**
implication in every finite group, hence (through Mal'cev residual finiteness
of finitely generated linear groups) in every exact finite-dimensional
unitary group. The new mathematics is not "find a quasi-identity"; the
repository already owns one, `mf-universal-horn-obstruction`, derived from the
established non-MF theorem. The new mathematics is the **modulus** turning
exact matrix validity into a dimension-free operator-norm estimate. If a
proof of `(OSM1)` were itself to run through rank-normalized supports,
Kazhdan corners, lamps or a compression, the route would forfeit its point;
`(OSM1)` is stated directly in `U(d)`.

## Attempts

1. **Specialize the general moduli.** If `matrix-restricted-burnside-gap`
   held for `(s,n)` it would give the power-law half; the relators `R_i`
   would then have to be folded in. That is the wrong order of difficulty --
   this claim is meant to be the *cheaper* target, reachable without the full
   restricted Burnside family. Recorded as an implication, not as an attack.

2. **Quote the finite-group stability node.** `finite-group-opnorm-support-profile`
   supplies a dimension-free correction once a finite group and presentation
   are fixed. Here the hypothesis does not identify a finite group: it is the
   `R_i` of an infinite group together with power tests. Dies at the same
   place as attempt 1 of `matrix-restricted-burnside-gap`.

3. **Compactness.** Gives `eta = eta(d)` only, as in attempt 2 there.

4. **Extract the modulus from Osin's proof.** Not attempted here, and the
   most promising unexplored direction: the separator is produced by small
   cancellation over a Burnside quotient, so the exact derivation of the
   conclusion from the hypotheses is by explicit van Kampen diagrams. A
   diagram of bounded area gives a modulus by the triangle inequality alone
   -- each relator substitution costs its own defect. The obstacle is that
   the derivation is *not* a finite sequence of relator applications: it is
   valid only in finite groups, so there is no van Kampen diagram to bound.
   That is exactly the same wall as attempt 1, seen from the group side.
