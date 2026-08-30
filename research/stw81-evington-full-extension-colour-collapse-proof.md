---
rg: 2
id: stw81-evington-full-extension-colour-collapse-proof
kind: route
title: Collapse the extension estimate with Evington's full-extension theorem
target: stw81-full-af-by-oinfinity-extensions-are-one-dimensional
requires:
  - stw81-continuous-trace-shadow-invariant
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Evington, [*Nuclear dimension of extensions of O-infinity-stable
algebras*](https://arxiv.org/abs/2012.03650), Theorem 1, proves that if

```text
0 -> J -> A -> B -> 0
```

is a full extension, `J` is separable and stable, and `B` is separable,
nuclear, and O-infinity-stable, then

```text
1 <= dim_nuc(A) <= dim_nuc(J)+1.                 (1)
```

Here fullness is exactly fullness of the Busby map: every nonzero positive
element of `B` has norm-full image in the corona `Q(J)`.  These are the
hypotheses of the present claim.  Since an AF algebra has nuclear dimension
zero, (1) becomes

```text
1 <= dim_nuc(A) <= 1,
```

and hence `dim_nuc(A)=1`.  Notice that separability of `A` follows from
separability of `J` and `B`: a countable dense set in `J`, together with
countably many lifts of a dense set in `B`, generates a separable dense
subalgebra of `A`.

The established lower bound

```text
ctdim(A) <= dim_nuc(A)
```

therefore gives `ctdim(A)<=1`.  By
`stw81-continuous-trace-shadow-invariant`, this is equivalent to saying that
every commutative hereditary C-star subalgebra of every quotient of `A` has
primitive spectrum of covering dimension at most one.  Thus the LXXXI
hypothesis is automatic for this extension class; it is not an additional
assumption.

For a concrete genuinely non-type-I family, use the Toeplitz--Cuntz
extension

```text
0 -> K -> T_n -> O_n -> 0,                       2 <= n < infinity.
```

The ideal `K` is separable, stable, and AF.  The quotient `O_n` is nonzero,
separable, nuclear, simple, purely infinite, and O-infinity-stable.  The
extension is unital, and Evington observes that a unital extension with
simple quotient is full.  Hence `dim_nuc(T_n)=1`, and the preceding argument
also verifies every LXXXI hereditary shadow of `T_n`.

**Trust boundary.**  This route does not use the conjectural maximum formula
of Problem LXXXII.  The no-extra-color conclusion is imported precisely from
Evington's theorem and depends on all three special features: stability of
the ideal, O-infinity-stability of the quotient, and fullness of the
extension.  No analogous conclusion is asserted after dropping any of
them.
