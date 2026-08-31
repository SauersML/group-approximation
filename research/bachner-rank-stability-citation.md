---
rg: 2
id: bachner-rank-stability-citation
kind: route
title: Apply Bachner's amenable group-algebra stability theorem
target: amenable-group-algebra-rank-stability-iff-rf
requires: []
---

Source: Benjamin Bachner, *Linear sofic representations of amenable
algebras*, arXiv:2602.05039v3, Theorem 1.2, equivalently Theorem 6.4(2).

In the paper's standing setup the algebra is finitely generated. Specialized
to a group algebra, the theorem says: if `Gamma` is finitely generated,
torsion-free and amenable, and `K[Gamma]` has no zero divisors, then
`K[Gamma]` is weakly stable if and only if `Gamma` is residually finite.

The forward direction uses weak stability to replace a maximally separating
linear-sofic representation by genuine finite-dimensional representations,
which make `Gamma` residually linear; finite generation lets Malcev's
theorem give residual finiteness. For the reverse direction, residual
finiteness supplies genuine matrix representations forming a linear-sofic
representation; the unique-conjugacy theorem for the amenable domain shows
that every linear-sofic representation is rank-conjugate to such a genuine
sequence.

The finite-generation, torsion-free, and domain hypotheses are retained.
Although the displayed sentence of Theorem 1.2/6.4(2) does not repeat finite
generation, Section 2 fixes a finitely generated algebra throughout and
Definition 6.2 uses its finite generating set. No Kaplansky zero-divisor
conjecture is silently invoked.

Status: arXiv preprint, v3, revised 2026-05-27. The standing setup, full
theorem statement, and Section 6 proof were checked 2026-08-31.
