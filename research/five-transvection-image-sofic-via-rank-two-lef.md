---
rg: 2
id: five-transvection-image-sofic-via-rank-two-lef
kind: route
title: The five-transvection image lies in the SL_2 symbol preimage over F_3, which is LEF by the twisted mirror fold
target: jacobson-image-of-five-transvection-group-is-sofic
requires:
  - binary-jacobson-rank-two-elementary-group-is-lef
  - five-transvection-group-acts-on-jacobson-half-line
artifacts:
  - experiments/jacobson-rank-two-2026-09-17/five_transvection_f3_fold.py
---

## Proof

Take `C = Z/3Z` in `binary-jacobson-rank-two-elementary-group-is-lef`. Then
`J_C = F_3<S,T | TS = 1>` is the algebra of the target claim, and
`T_(F_3) = π^(-1) SL_2(F_3[ζ, ζ^(-1)])` is LEF.

Item 4 of `five-transvection-group-acts-on-jacobson-half-line` says the symbol
map sends `Γ_V` into `SL_2(F_3[ζ, ζ^(-1)])`. It can also be checked directly on
the generators:

* the four transvections have unipotent symbols;
* `(Se)^2 = S(eS)e = 0`, since `eS = S - S(TS) = 0`, so `1 + Se` is a unit with
  inverse `1 - Se`;
* the symbol of `diag(1, 1 + Se)` is `I`, since `e` has symbol `0`.

So `Γ_V <= T_(F_3)`. LEF passes to subgroups, so `Γ_V` is LEF.

An LEF group is sofic. Given a finite `F`, take an injective partial
homomorphism `θ : F -> H` into a finite group, and let `H` act on itself by
left translation. Then `θ(gh) = θ(g)θ(h)` holds exactly on `F`, and distinct
elements of `F` go to permutations with no common value at any point, so they
are at normalized Hamming distance `1`. This is a sofic approximation. So
`Γ_V` is sofic.   □

**Explicit models.** `θ_N` is `(FOLD)` with `w = [[0,1],[-1,0]]`, and
`φ(g) = w^(-1) (g^(-1))^T w`, into `GL_(2N)(F_3)`. The artifact checks, over
`F_3`, the following:

* exact multiplicativity on 150 random words in the ten generators and their
  inverses, at `N = 48`;
* that the eight defect elements `z^e x_23(1)^a x_12(1)^b` have eight distinct
  images, where `z -> -I`, `x_23(1) -> diag(1, 1 + Se)` and
  `x_12(1) -> E_01(T)`;
* that the untwisted fold fails on 59 of the 150 words.

**Belief changed.** The target recorded that a proof "must be sofic but not
LEF-by-compression". That is false: the untwisted boundary compression fails,
but the twisted one is an exact LEF model. The chain then runs through
`weakly-finite-nonzero-defect-via-sofic-jacobson-image`, which with
`linear-sofic-group-algebra-is-stably-finite` gives
`five-transvection-group-has-weakly-finite-nonzero-defect`. That claim refutes
`four-transvections-and-x23-force-defect-vanishing`.
