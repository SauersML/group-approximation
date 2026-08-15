---
rg: 2
id: corona-commutant-growth-witness
kind: claim
title: Operator-norm relative commutants do grow under compression in residually finite coronas
distinct_from:
  corona-commutant-no-growth: That claim asserts the inclusion of relative commutants is always an equality; this one is its negation for the general statement, witnessed by an explicit slow-wall construction over any residually finite ambient group.
  corona-defect-is-not-uniform: That claim says corona representations only supply pointwise-vanishing defect; this one constructs an explicit element of the compressed commutant outside the full commutant.
artifacts:
  - notes/2026-08-15-unified-mf-compression-external.md
---

Credit: external review session (2026-08-15, GPT-assisted, unrefereed);
proof audited step-by-step by this session before commitment.

Let `H` be countable and residually finite, `L <= H` finitely generated,
and `L_1 = t L t^{-1} < L` a strict one-sided compression.  Then there is a
faithful corona representation `Theta : H -> U(Q)` built entirely from
finite quotients (regular representations), and a unitary `v in Q`, such
that

```text
v in Theta(L_1)' cap Q,     v notin Theta(L)' cap Q,
```

and all `H`-conjugates of `v` commute.  The hypothesis is compatible with
`L` having property (T).

**Consequences.**  The general form of `corona-commutant-no-growth` is
FALSE: property (T) does not give operator-norm relative-commutant
no-growth in a norm matrix corona.  The witness `v` is a slow phase ramp in
the compressed word metric: it is Hilbert--Schmidt invisible (its support
has vanishing normalized rank), so it never contradicts the formalized
transport theorem, and its spectrum fills an arc, exactly as
`spectral-component-motion-bound` requires of any survivor.  The refutation
does NOT hand the marked quotients an MF model: the construction needs
residual finiteness of `H`, and the marked quotients are not LEF
(`marked-quotients-not-lef`); those instances are resolved separately and
negatively by `commuting-lamp-quotient-not-mf` and
`literal-mark-quotient-not-mf`.
