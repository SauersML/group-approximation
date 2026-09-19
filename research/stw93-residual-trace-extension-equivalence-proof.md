---
rg: 2
id: stw93-residual-trace-extension-equivalence-proof
kind: route
title: Extend a residual trace through its multiplier algebra and use the factor quotient
target: stw93-residual-tracefree-iff-unique-trace
requires:
  - stw93-all-z-central-slices-generate-quasitrace-null-ideal
  - stw93-super-mcduff-tracial-central-quotient
artifacts:
  - research/artifacts/stw93-residual-bounded-trace-audit-2026-08-30.md
---

Every normalized trace on `D` annihilates `K_Z^sat`, because the latter is
annihilated by every normalized `2`-quasitrace.  Pullback along `D->E`
therefore identifies the normalized trace spaces of `D` and `E`.  This
proves that `(b)` and `(c)` are equivalent.

The quotient

```text
E/R = D/I
```

is a II_1 factor and hence has a unique normalized trace.  If `s` is a
normalized trace on `E` different from the canonical trace, then `s|R` is
nonzero: otherwise `s` factors through `E/R` and quotient uniqueness makes
it canonical.  Thus `(a)` implies `(b)`.

Conversely, suppose `theta` is a nonzero bounded trace on `R`.  It has a
canonical finite tracial extension `tilde(theta)` to `M(R)`, satisfying

```text
tilde(theta)(1)=||theta||.
```

The multiplication action gives a unital star homomorphism `E->M(R)`, even
if `R` is not essential.  Hence

```text
s=tilde(theta) o (E->M(R))
```

is a bounded trace on `E`, restricts to `theta`, and satisfies
`s(1)=||theta||>0`.  Its normalization charges `R`, so it differs from the
canonical trace.  Thus `(b)` implies `(a)` and all three statements are
equivalent.

**Trust boundary.**  This argument uses the finite multiplier extension of
a bounded trace, not an extension of an arbitrary quasitrace.  Accordingly
it settles the exact ordinary-trace obstruction but does not prove the open
quasitrace annihilation claim.
