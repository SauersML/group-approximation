---
rg: 2
id: gardam-complex-units-citation
kind: route
title: Import Gardam's nontrivial units of the complex group ring of the Promislow group
target: unit-conjecture-fails-over-complex-numbers
requires: []
---

**Source.** G. Gardam, *Non-trivial units of complex group rings*,
arXiv:2312.05240 (v1 8 Dec 2023, v2 29 Oct 2024),
<https://arxiv.org/abs/2312.05240>.

**Abstract (verbatim).** "The Kaplansky unit conjecture for group rings is
false in characteristic zero."

**Theorem A**, as read from the arXiv HTML rendering of v2: the torsion-free
group

```text
P = <a, b | b^(-1) a^2 b = a^(-2), a^(-1) b^2 a = b^(-2)>
```

has "non-trivial units" in `C[P]`, with an explicit unit of support size 21.
The introduction notes that a characteristic-zero counterexample gives
counterexamples in characteristic `p` for all but finitely many `p`.

**Identification.** This presentation is exactly the Promislow group used in
`promislow-radius4-one-sided-and-integral-separation`.

**Trust surface.** The statement was read through a web extraction of the
arXiv HTML v2 by the `zero-divisor-swarm` lane on 2026-09-12. The PDF text was
not extracted, and the unit itself was not recomputed here.
