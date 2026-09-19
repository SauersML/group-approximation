---
rg: 2
id: agent-bcl-two-kazhdan-literature-audit
kind: route
title: Audit the higher-cohomology hypotheses and the Frobenius normalization on the BCL wordization
target: agent-bcl-two-kazhdan-route-misses-group-and-metric
requires:
  - agent-free-compressor-full-corner-root-is-fd-invisible
  - hs-stability-plus-fd-residual-forces-nonhyperlinearity
---

Ershov--Jaikin-Zapirain, *Property (T) for noncommutative universal
lattices*, arXiv:0809.4095, Theorems 1.1 and 6.2, prove property `(T)` for
`EL_n(R)` and `St_n(R)` for every finitely generated unital associative ring
`R` and every `n>=3`.  This applies to `R_BCL`, but the paper proves no
degree-two unitary-cohomology vanishing.

De Chiffre--Glebsky--Lubotzky--Thom, *Stability, cohomology vanishing, and
non-approximable groups*, arXiv:1711.10238, Theorem 1.2, deduce Frobenius
stability from finite presentation and 2-Kazhdan vanishing.  Their Frobenius
norm is explicitly

```text
||T||_F=(sum_(i,j)|T_ij|^2)^(1/2),
```

with no factor `d^(-1/2)`.  Their splitting engine requires a
submultiplicative norm; the normalized Hilbert--Schmidt norm is explicitly
outside that hypothesis.  Formula `(B2K2)` is a direct dimension-one-corner
witness that normalized microstate error gives no Frobenius-small error.

Bader--Sauer, *Higher Kazhdan property and unitary cohomology of arithmetic
groups*, arXiv:2308.06517, prove higher unitary-cohomology vanishing for
simple Lie groups and arithmetic/lattice settings.  Their hypotheses do not
cover Steinberg groups over arbitrary finitely presented noncommutative
rings.  Glebsky--Lubotzky--Monod--Rangarajan, *Asymptotic Cohomology and
Uniform Stability for Lattices in Semisimple Groups*, arXiv:2301.00476,
likewise assumes semisimple-lattice geometry and submultiplicative matrix
norms.  Neither theorem applies to `R_BCL` or to normalized HS.

Finally, Fournier-Facio, *Stability, approximable quotients, and higher
property (T)*, arXiv:2512.09180v2, explicitly separates property `(T)`,
Frobenius stability, and property `(T_2)`, and supplies quotient phenomena
showing that degree-two vanishing cannot be passed through the BCL ring
quotient as ordinary property `(T)` can.

The compressor-unit fork is formal.  A coefficient unit already belongs to
the Steinberg coefficient system and naming its standard word is a Tietze
extension.  An independent stable letter is instead a group extension, for
which none of the cited theorems supplies permanence.  This proves every
part of the claim.
