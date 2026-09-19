---
rg: 2
id: goldbring-sinclair-max-u-group-witness-is-trace-blind
kind: claim
title: The separable Goldbring-Sinclair max-U witness is a sofic full group algebra with incompatible canonical and non-CE traces
distinct_from:
  max-tensor-definability-forces-ultraproduct-lifting: That records the general definability and max-U obstruction; this identifies the explicit separable witness as a full group algebra of a sofic group and audits its traces.
  non-ce-trace-on-sofic-racg: That pulls one fixed BCS trace to an explicit finitely presented sofic Coxeter group; this uses Goldbring-Sinclair's max-U witness, which is countable rather than finitely generated and is additionally surjectively universal.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: That gives a general character-face obstruction and a free-product example; this proves that even the paper's explicit operator-norm max-U failure coexists with an embeddable canonical group trace.
  nonce-factor-in-group-factor-corner-forces-nonhyperlinear: That is the positive endpoint if a non-CE factor embeds in a canonical group-factor corner; this proves such a corner embedding is impossible for the Goldbring-Sinclair witness despite its non-CE factorial traces.
artifacts:
  - research/artifacts/goldbring-sinclair-max-u-trace-blindness-2026-08-23.md
  - research/artifacts/goldbring-sinclair-tensor-definability-audit-2026-08-23.md
---

**ESTABLISHED.**  There is an explicit countable sofic group `Gamma` such
that:

1. `C^*(Gamma)` is the separable algebra in Goldbring--Sinclair Theorem
   3.23 and fails property `max-U` for every cofinal ultrafilter in that
   theorem;
2. the canonical trace of `Gamma` is Connes embeddable;
3. `C^*(Gamma)` is surjectively universal and carries a factorial trace
   `sigma` whose GNS factor is not Connes embeddable; and
4. that non-CE GNS factor does not embed into any nonzero corner of
   `L(Gamma)`.

Take `G=SL_3(Z)`, `H=F_infinity*G`, and `D=C^*(H)`.  For each nonempty
finite `J subset N`, Goldbring--Sinclair use `D_J=D^(|J|)` and
`A=*_(J)D_J`.  Since

```text
D^m = C^*(H) tensor_max C^*(C_m) = C^*(H x C_m),
```

the full free-product universal property identifies

```text
A = C^*(Gamma),
Gamma=*_(nonempty finite J subset N) (H x C_(|J|)).
```

Ioana--Spaas--Wiersma prove that `C^*(SL_3(Z))` fails LLP and hence LP, so
Goldbring--Sinclair Theorem 3.23 applies.  On the other hand, all factors in
the displayed free product are sofic, and soficity is preserved by the
displayed operations.  Thus `Gamma` is sofic and its canonical trace is CE.

Surjective universality comes from the `C^*(F_infinity)` free factor.  Pull
back a trace generating a separable-predual non-CE finite factor through a
quotient of `C^*(Gamma)`.  This gives `sigma`.  If its GNS factor embedded in
a corner of `L(Gamma)`, CE of `L(Gamma)` and permanence under corners and
subalgebras would make that factor CE, a contradiction.

Therefore failure of property `max-U` is canonically trace-blind: it cannot
by itself imply nonhyperlinearity or localize a non-CE payload into the
canonical group factor.  The example does generate a non-CE factor through
an ordinary group representation, but its character is necessarily
nonregular.

