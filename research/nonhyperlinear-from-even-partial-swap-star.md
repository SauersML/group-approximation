---
rg: 2
id: nonhyperlinear-from-even-partial-swap-star
kind: route
title: Use one even partial-swap star as the finite Hilbert-hotel breaker
target: non-hyperlinear-group
requires:
  - even-partial-swap-star-has-canonical-trace-floor
  - common-source-orthogonal-partial-swap-star-compiler
---

Let `Gamma` and `h=j_1j_2` be supplied by the compiler.  Exact infinite
completeness sends `h` to the nontrivial three-cycle on the source and two
orthogonal range copies, so `h!=1_Gamma`.

If `Gamma` were hyperlinear, canonical-trace microstates `U_n` would satisfy

```text
def_R(U_n)->0,
tr(h(U_n))->0.                                         (NSS1)
```

The compiler decodes the two common-source swaps.  The binary case of the
even-star trace theorem instead gives

```text
Re tr(h(U_n))>=1/4-o(1),                               (NSS2)
```

contradicting `(NSS1)`.  Therefore `Gamma` is non-hyperlinear.

No self-reference or unbounded test family is required after the compiler.
The user's error-spreading mechanism is literal here: one source is copied
into incompatible regions, and adding an even number `k` of children raises
the forced trace floor to `(k-1)/(2k)`.
