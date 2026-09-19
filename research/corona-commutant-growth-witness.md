---
rg: 2
id: corona-commutant-growth-witness
kind: claim
title: Operator-norm relative commutants do grow under compression in residually finite coronas
distinct_from:
  corona-commutant-no-growth: That claim asserts the inclusion of relative commutants is always an equality; this one is its negation for the general statement, witnessed by an explicit slow-wall construction over any residually finite ambient group.
  corona-defect-is-not-uniform: That claim says corona representations only supply pointwise-vanishing defect; this one constructs an explicit element of the compressed commutant outside the full commutant.
  commutant-no-growth: That established claim proves no-growth for genuine finite-dimensional representations; this one proves growth happens in the norm corona, so the exact statement fails to pass to the asymptotic setting.
  marked-quotient-mf-forces-commutant-growth: That established claim is the algebraic implication that MF-ness of the marked quotients would force growth; this one exhibits growth unconditionally in a different, residually finite ambient, independent of any MF hypothesis.
  relative-wall-commutant-growth: That established claim is the target-independent equivalence between relative walls and commutant growth; this one constructs the growth in the specific operator-norm corona target, refuting the no-growth conjecture there.
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
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
