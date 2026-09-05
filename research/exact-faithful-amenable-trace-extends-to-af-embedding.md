---
rg: 2
id: exact-faithful-amenable-trace-extends-to-af-embedding
kind: claim
title: A separable exact C*-algebra with a faithful amenable trace embeds in a simple AF algebra with the trace extending
distinct_from:
  tww-gabe-schafhauser-af-embedding-theorem: that is the same statement under the UCT, proved by Tikuisis--White--Winter, Gabe and Schafhauser; this drops the UCT and is the form STW footnote 26 says would settle Problem X for exact algebras.
  stw99-problem-viii-exact-quasidiagonal-af-embeddable: that starts from a quasidiagonal algebra and asks for an AF embedding; this starts from a faithful amenable trace, which is a priori weaker than quasidiagonality, and asks for an embedding extending the trace.
  stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable: that assumes the trace is already quasidiagonal; this assumes only amenability of the trace, so it implies IX(2) together with the trace statement it is designed to settle.
artifacts:
  - research/artifacts/stw10-x1-exact-residual-2026-09-05.md
---

Let `A` be a separable exact C\*-algebra with a faithful amenable tracial
state `tau`.  Then there are a unital simple AF algebra `D`, an injective
*-homomorphism `iota : A -> D`, and a tracial state `tau_D` on `D` with
`tau_D o iota = tau`.

**OPEN.**  This is Theorem 11 of Schafhauser--Tikuisis--White without the UCT,
in the trace-extending form that Schafhauser proves under the UCT
(`tww-gabe-schafhauser-af-embedding-theorem`).  STW footnote 26 records that
this stronger, UCT-free form is what their reduction of Problem X(1) for exact
algebras actually needs.

## Attempts

- Under the UCT this is a theorem.  Every known proof passes through
  classification-type uniqueness results for maps into the ultrapower of a
  UHF or AF algebra, which is where the UCT enters; no UCT-free proof is
  recorded.
- The statement implies `stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable`
  directly (a quasidiagonal trace is amenable) and
  `amenable-traces-on-exact-cstar-algebras-are-quasidiagonal` through
  `exact-x1-via-uct-free-trace-extending-af-embedding`.
