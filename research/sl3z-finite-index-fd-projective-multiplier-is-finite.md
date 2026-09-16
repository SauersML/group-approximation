---
rg: 2
id: sl3z-finite-index-fd-projective-multiplier-is-finite
kind: claim
title: Every finite-index subgroup of SL_3(Z) has only finitely many finite-dimensionally realizable scalar classes
distinct_from:
  sp4-finite-index-fd-projective-multiplier-is-finite: that is the same statement for Sp_4(Z), whose level-one multiplier has rank one; this is SL_3(Z), where the level-one input is van der Kallen's finite multiplier and the Lie algebra is sl_3.
  sl3z-schur-multiplier-is-klein-four: that is level one only, where H_2 itself is finite; this is every finite-index subgroup, whose real H^2 may be nonzero, and asserts finiteness only of the classes that finite dimensions can see.
  finite-fd-multiplier-projective-models-round-strictly: that is the abstract rounding consequence of finite realizable multiplier; this verifies the finiteness hypothesis at every finite-index subgroup of SL_3(Z).
artifacts:
  - experiments/sl3z-finite-index-multiplier-2026-09-16/sl3-chevalley-eilenberg-betti.py
---

**ESTABLISHED (unreviewed).** Let `K` be a finite-index subgroup of `SL_3(Z)` and

```text
R(K) := { [c] ∈ H^2(K; T) : c is the exact 2-cocycle of some projective unitary
          representation K -> U(d), d < ∞ }.
```

Then `R(K)` is finite. More precisely, the natural map

```text
H^2_cts(K^, Q/Z)  -->  H^2(K; T)                                           (SF1)
```

is injective with image exactly `R(K)`, and its source is finite.

Derivation: `sl3z-finite-index-multiplier-lazard-whitehead-proof`.

**The picture.**
- **What finite dimensions see.** Finite-dimensional unitary representations see only the
  profinite completion. By the congruence subgroup property that completion is an open subgroup
  of `prod_p SL_3(Z_p)`.
- **Primes dividing the level.** At these primes, infinitely many classes could only come from
  second Lie algebra cohomology. `H^2(sl_3, Q_p) = 0` (Whitehead; the artifact computes the
  Betti numbers `(b_1, b_2, b_3) = (0, 0, 1)` exactly over `Q`), and Lazard turns this vanishing
  into finiteness.
- **Remaining primes.** Their product is a direct factor of `SL_3(Z^)`. It is handled at once
  by van der Kallen's `H_2(SL_3(Z); Z) = Z/2 × Z/2`.

**Consequences.**
- **Strict rounding of exact projective models.** With
  `finite-fd-multiplier-projective-models-round-strictly`, every exact finite-dimensional
  projective model `α_n` of `K` with cocycles tending to 1 pointwise is, for large `n`, a scalar
  gauge `β_n π_n` of genuine representations, with `β_n -> 1`. That node's hypothesis that
  `H_2(K; Z)` be finitely generated holds because `K` is finitely presented.
  - So Dogon's Theorem 3.1 mechanism (arXiv:2211.10492v3), realized by exact
    finite-dimensional twisted representations, produces no instability at any finite-index
    subgroup of `SL_3(Z)`.
  - The same holds for the Heisenberg-cover mechanism of `rf-kazhdan-group-not-flexibly-hs-stable`.
- **Bounded centres.** `sl3z-finite-index-z-extension-centres-stay-bounded`.

**The case that tells you something.** `H^2(K; T)` may still contain circles.
- Suppose `b_2(K) > 0` for some congruence subgroup `K`. Then `exp_*(H^2(K; R))` is an infinite
  subgroup of `H^2(K; T)`.
  - It is the quotient of `H^2(K; R) != 0` by the image of `H^2(K; Z)`.
  - Evaluation on a suitable `x ∈ H_2(K; Z)` sends that image into `Z` but `H^2(K; R)` onto
    `R`, so the quotient is nonzero.
  - A nonzero quotient of a real vector space is divisible, hence infinite.
- By (SF1) only finitely many of its points are realized in finite dimensions.
- Whether any congruence subgroup of `SL_3(Z)` has `b_2 > 0` is not decided here. The literature
  on the cohomology of congruence subgroups of `SL_3(Z)` is recalled from memory as containing
  such levels, but it was not fetched and is not used.

**Not claimed.** No bound on `|R(K)|` in terms of the index.
