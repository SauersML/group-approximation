---
rg: 2
id: bgv-adversarial-fault-tolerance-citation
kind: route
title: Import almost-linear adversarial quantum fault tolerance by joint subsystem-product encoding
target: bgv-adversarial-fault-tolerance
requires: []
artifacts:
  - research/artifacts/two-august-2026-anti-localization-papers-2026-08-20.md
---

**Established by citation.**  Breuckmann--Golowich--Vazirani,
arXiv:2608.16857v1, Theorem 7.1 (and its informal Theorem 1.1) constructs a
constant-alphabet fault-tolerance scheme which compiles a circuit on `Nbar`
logical qudits using polynomial space and subpolynomial depth overhead, and
which tolerates arbitrary corruptions on

```text
N / 2^(O(sqrt(log Nbar))) = N^(1-o(1))
```

physical qudits at every time step.  The noise may be global, worst-case,
temporally correlated and non-Markovian.

The construction jointly encodes the logical qudits rather than placing each
one in a separately attackable block.  Theorem 4.2 gives the product lower
bounds for the subsystem-code distances; Proposition 3.3 imports local
testability of the underlying classical tensor-product codes; Lemma 5.2 uses
that filling estimate in single-shot error correction; and Theorem 7.1 uses
recursive simulative composition to return to constant physical alphabet.

This citation concerns a specified tensor-site adversarial noise model.  It
does not identify normalized Hilbert--Schmidt defect with corrupted sites in
an arbitrary approximate group representation.
