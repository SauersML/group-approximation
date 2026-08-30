---
rg: 2
id: sofic-chart-quotient-forces-character-energy-floor
kind: claim
title: A seed-preserving sofic chart quotient forces a global character-energy floor
artifacts:
  - research/artifacts/sofic-chart-character-energy-floor-2026-08-30.md
distinct_from:
  sofic-action-gives-marked-pauli-central-product-microstates: that constructs marked Pauli microstates; this extracts an exact whole-module Fourier representation from their first lamp coordinate and proves a quantitative global transport floor.
  global-schreier-pvm-is-stronger-than-action-soficity: that proves a supplied vanishing-energy PVM has zero mass; this constructs the finite chart adversaries and turns that estimate into a no-decoder theorem.
  finite-covariance-energy-sees-only-character-restrictions: that gives an algebraic two-character swap for one finite probe set; this realizes a moving-word leak inside genuine sofic action charts for every finite word window.
  sofic-actor-refutes-lamp-character-transport: that treats the regular Tarski lamplighter conditional on actor soficity; this applies to any sofic set action with a uniform seed-visible Schreier gap.
---

**ESTABLISHED.** Let a countable group `A` act on a countable set `X`, let

```text
M subset direct_sum_X F_2
```

be an `A`-invariant submodule, and fix `0!=m_0 in M`.  Let `S` be a finite
symmetric actor set.  Assume that every character `chi in M^` with

```text
chi(m_0)=-1
```

has an infinite `A`-orbit whose normalized `S`-Schreier operator has bottom
gap at least one common `gamma>0`.

If the set action `A action X` is sofic, then for every finite actor/module
word window there are finite-dimensional unitaries `C_s^(n)` and exact
representations

```text
rho_n:M -> U(d_n)
```

such that every actor relation and every covariance relation in that fixed
window has normalized-HS defect tending to zero, while

```text
tr_(d_n)(1_(-1)(rho_n(m_0))) -> 1/2                     (SCQ1)
```

and the complete character-transport energy satisfies

```text
E_n=(1/|S|) sum_(s in S) sum_(chi in M^)
 ||C_s^(n) P_chi^(n) (C_s^(n))^*-P_(s chi)^(n)||_2^2
 >= gamma-o(1).                                         (SCQ2)
```

By the whole-module averaging identity, these same tuples have a moving
module word `m_n` and an actor generator `s_n` with

```text
||C_(s_n)^(n) rho_n(m_n) (C_(s_n)^(n))^*
       -rho_n(s_n m_n)||_2
 >= sqrt(gamma)-o(1),                                   (SCQ3)
```

even though the covariance defect of every fixed module word tends to zero.

The obstruction is robust under changing the exact module representation.
If another exact `rho'_n:M->U(d_n)` satisfies

```text
||rho'_n(m_0)-rho_n(m_0)||_2 ->0,
```

then its seed-negative spectral mass still tends to `1/2`, and its complete
transport energy also satisfies `(SCQ2)`.  Consequently no
dimension-independent finite-relator decoder which preserves `m_0` can make
the global transport energy tend to zero on these chart tuples.

Quantitatively, a chart retaining seed-negative mass at least
`(1-alpha)/2` has `E_act>=gamma(1-alpha)`.  If a replacement exact module
representation changes the seed by normalized-Hilbert--Schmidt distance at
most `tau`, the same argument gives the robust bound

```text
E'_act>=gamma(1-alpha-tau).                            (SCQ4)
```

Thus the obstruction survives any seed-preserving decoder with a uniform
error tending to zero.

The conclusion applies to any fixed packet whose relations survive a
seed-preserving chart quotient which is the identity on `M rtimes A`.  If
`A` is also sofic, the bare Pauli-seed quotient from
`sofic-action-gives-marked-pauli-central-product-microstates` supplies such
tuples while keeping the common mark at Hamming distance one.

This does not refute
`infinite-character-actor-word-energy-interface`: a successful packet may
use a nonsofic action or controller relations destroyed by the chart
quotient.  It proves that one of those two escapes is mandatory.
