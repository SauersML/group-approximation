---
rg: 2
id: boolean-relations-have-affine-complete-rstar-pp-gadgets
kind: claim
title: Every Boolean relation has one R-star pp gadget containing all affine-safe cap branches
distinct_from:
  affine-safe-support-admits-a-tailored-rstar-cap-pp-lift: that chooses a separating character after fixing one affine support; this puts every nonzero character into one gadget, which is independent of the support.
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that forbids one cap profile from covering a full nonaffine relation; this uses different profiles for its different affine subrelations.
  rstar-core-character-profiles-induce-an-exact-affine-cover: that describes the cover induced by an arbitrary fixed gadget; this constructs a fixed gadget whose cover is complete for every affine-safe subset.
---

**ESTABLISHED UNIFORM AFFINE-COMPLETE PP COMPILER.**  For every nonempty
Boolean relation `C subseteq F_2^n`, one can effectively construct a single
finite pp gadget `G_C` over `R_*`, depending only on the truth table of `C`,
such that:

```text
visible projection of G_C = C,                          (UAC1)

S subseteq C has a deterministic cap-valued witness
section through G_C     iff     Aff(S) subseteq C.       (UAC2)
```

The size is bounded by a function of `n`.  In particular, for the bounded
answer length in Culf--Mastel, these gadgets are uniform constant-size
choices and may replace the unspecified NP-completeness gadgets without
knowing the positive support of the perfect trace.

## One universal forbidden-point gadget

Fix `b notin C` and put `u=x+b`.  Introduce, for **every** nonzero linear
functional `lambda:F_2^n->F_2`, the affine bit

```text
s_lambda=lambda(u).                                    (UAC3)
```

Then

```text
u!=0     iff     OR_(lambda!=0) s_lambda=1.             (UAC4)
```

The reverse implication is immediate.  For the forward implication, a
nonzero vector is detected by some linear functional.  Convert the fixed
wide OR in `(UAC4)` to a standard 3-CNF chain and encode each ternary OR as

```text
OR(a,b,c)     iff     exists t, R_*(t,a,b,c).            (UAC5)
```

All translations, characters, complements, and partial sums are compiled
by the fixed-cap xor rows from
`dfnqxy-nonverify-rows-have-cap-safe-rstar-pp-compilers`.

Now let `A subseteq F_2^n minus {b}` be affine.  Some nonzero character
`lambda_A` is identically one on `A+b`.  In the wide-OR chain, choose the
chain bits to be constant `1` before the occurrence of `s_(lambda_A)` and
constant `0` after it.  Every 3-clause then has one literal identically
equal to `1`.  All its other literals and its parity-determined tail `t` are
affine functions on `A`.  Hence the row image is an affine subset of `R_*`
and therefore a Fano cap.

Conjoin this same universal forbidden-point gadget over every `b notin C`.
It defines exactly `C`.  Given any affine `A subseteq C`, independently route
the chain for each forbidden `b` through a character separating `A+b` from
zero.  The auxiliary sets are private, so these routes concatenate to a
cap-valued witness section on `A`, and hence on every `S subseteq A`.
Necessity in `(UAC2)` is
`fano-cap-witness-sections-force-source-affine-safety`.

For a perfect commuting source context, every witness bit in the selected
branch is affine on `Aff(S)` and is therefore a product of the original
commuting involutions and a scalar sign.  The lift stays in the original
finite tracial algebra.  Because `G_C` is computed from `C`, not from `S`,
this is compatible with a succinct uniform reduction whenever the source
arity is bounded.
