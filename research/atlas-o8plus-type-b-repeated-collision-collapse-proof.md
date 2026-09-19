---
rg: 2
id: atlas-o8plus-type-b-repeated-collision-collapse-proof
kind: route
title: Expose the normal Klein four and collapse its universal multiplicity algebra
target: atlas-o8plus-type-b-repeated-collision-collapse
requires:
  - atlas-o8plus-canonical-moved-module-completion-fails
  - atlas-collision-local-presentation-is-s4
artifacts:
  - experiments/atlas_a4_collision_local_universal_s4.g
  - experiments/atlas_a4_repeated_module_collision.g
  - experiments/atlas_a4_q1920_o8p_discovery.g
  - experiments/atlas_a4_q1920_o8plus_typeb_repeated_v4.g
  - research/artifacts/atlas-a4-o8plus-type-b-repeated-v4-gbnp.txt
  - research/artifacts/atlas-a4-o8plus-type-b-repeated-v4-gbnp.json
---

## The lower-degree presentation is exactly equivalent

Let `F=<t,s,c>` be free subject only to the marked `S3` relations on `t,s`.
The original collision presentation adds

```text
c^2=1,       (ct)^3=1,       t c s c t^-1 c s t c=1.       (O8B-1)
```

The exact GAP certificate computes order 24 for this quotient.  Now replace
the last two relations by the normal-Klein-four relations

```text
c^s=c^t,                  c c^t=c^(t^2).                    (O8B-2)
```

GAP independently computes order 24 for this second quotient.  The same
marked permutation tuple maps both quotients onto `S4` of order 24.  Hence in
both cases the kernel in `F` is exactly the kernel of that marked epimorphism
to `S4`; the two normal closures are equal.  Thus `(O8B-1)` and `(O8B-2)`
define the same representations over every field and in every dimension.
This certifies both directions of the replacement, rather than using an
identity observed only in one chosen S4 image.

## The free coefficients represent every multiplicity

The exact A-module decomposition is

```text
H|_A = 1^4 + U^2,                 End_A(U)=F2.
```

Therefore

```text
End_A(H^m) ~= M_(4m)(F2) x M_(2m)(F2)
            ~= (M_4(F2) tensor M_m(F2))
                x (M_2(F2) tensor M_m(F2)).                (O8B-3)
```

Fix the sixteen matrix units of `M4` and the four matrix units of `M2`.
Every A-central `C` on `H^m` is uniquely obtained by attaching arbitrary
coefficient matrices `X_0,...,X_19 in M_m(F2)` to those units.  Accordingly,
the generic operator over

```text
R=F2<x_0,...,x_19>
```

is functorial in `m`: the evaluation `x_i -> X_i` gives every point of
`End_A(H^m)`, with no commutativity assumption on the coefficient matrices.

## The two-sided certificate

Substitute the generic `C` into `C^2=I` and the matrix versions of `(O8B-2)`:

```text
S^-1 C S = T^-1 C T,
C (T^-1 C T) = T^-2 C T^2.                              (O8B-4)
```

All entries have degree at most two in `R`.  For the two marked Type-B
twists, there are respectively 129 and 119 distinct nonzero entry relations.
GBNP 1.1.0 computes the strong two-sided Groebner basis in each case as

```text
x0+1, x1, x2, x3, x4, x5+1, x6, x7, x8, x9,
x10+1, x11, x12, x13, x14, x15+1, x16+1, x17, x18, x19.
```

Thus every coordinate of `C-I` belongs to the two-sided relation ideal in
the free associative algebra itself.  This is stronger than vanishing after
a scalar or commuting specialization.  Evaluating the displayed ideal
membership at arbitrary coefficient matrices `X_i in M_m(F2)` gives `C=I`
for every `m`, proving the claim.
