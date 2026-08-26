---
rg: 2
id: maslov-mod3-gap-is-metaplectic-base-degree-six-gap
kind: claim
title: The mod-three Maslov gap is exactly the invisible Z3 extension gap over the metaplectic double cover
distinct_from:
  deligne-sector-gap-is-exactly-nonhyperlinearity: that identifies the mod-three projective gap with nonhyperlinearity of the triple cover; this transports the same gap to the degree-six cover and exhibits its residually finite metaplectic base.
  metaplectic-half-parameter-is-ce: that proves hyperlinearity of the degree-two cover; this combines the half-parameter with the mod-three parameter and gives quantitative tensor reductions between the one-third and one-sixth sectors.
  hs-stability-forces-nonhyperlinear-central-extension: that consumes Hilbert--Schmidt stability of a base to obtain some nonhyperlinear finite central quotient; this is an unconditional equivalence for the specific degree-six extension but supplies no stability theorem for its base.
---

**ESTABLISHED.**  Let `E_infinity` be the inverse image of `Sp_4(Z)` in the
universal cover of `Sp_4(R)`, with central generator `z`, and put

```text
E_q=E_infinity/<z^q>.
```

Then the degree-six cover fits into

```text
1 -> <z^2> = Z/3 -> E_6 -> E_2 -> 1,                   (M6G1)
```

where `E_2` is the residually finite metaplectic double cover and `<z^2>` is
the full finite residual of `E_6`.  Moreover the following are equivalent:

1. `E_3` is hyperlinear;
2. `E_6` is hyperlinear;
3. `1/3` belongs to the Maslov CE parameter subgroup `E_CE`;
4. `1/6` belongs to `E_CE`.

The equivalence is quantitative at the projective-presentation level.  A
vanishing-defect sequence in the one-third sector gives one in the one-sixth
sector after tensoring with one fixed exact metaplectic half-projective
representation and complex conjugating.  Conversely, squaring tensorially a
one-sixth sequence gives a one-third sequence, with at most twice the defect.
Thus a positive dimension-uniform gap exists at `1/3` if and only if one exists
at `1/6`.

Consequently `maslov-mod3-projective-defect-gap` can equivalently be attacked
as follows: prove that the finite central extension `(M6G1)` of the **residually
finite Kazhdan group** `E_2`, whose order-three kernel is invisible in every
finite quotient, is nonhyperlinear.  This is a relocation of the exact open
obstruction, not a proof from residual finiteness or property `(T)` alone.

The proof is `maslov-mod3-degree-six-tensor-equivalence-proof`.
