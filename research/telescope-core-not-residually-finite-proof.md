---
rg: 2
id: telescope-core-not-residually-finite-proof
kind: route
title: Two-divisibility of the telescope collapses levels without a stable letter
target: telescope-core-not-residually-finite
requires: [literal-telescope-core-lef, literal-lamp-kernel-clifford-block-amalgam]
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

Found by `cairn-verify2` while stress-testing Lemma 3.1 of
`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` against Theorem 9.1 of
`notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md`.  The LEF
half is `literal-telescope-core-lef`; only the failure of residual finiteness
is proved here.

*Step 1: every finite quotient of `T` alone collapses the levels.*  Let
`phi : T -> F` be a homomorphism to a finite group, and let
`A = Z[1/2]^3 normal_in T` be the translation subgroup.  Then `phi(A)` is a
finite abelian group and is 2-divisible, because `A = 2A`.  A finite
2-divisible abelian group has odd order: its 2-primary part `P` satisfies
`2P = P`, and a finite abelian 2-group with that property is trivial.  So `2`
is invertible on `phi(A)`, and for `u in Z^3` and `k >= 0` the element
`phi(2^{-k} u)` is the unique `y` with `2^k y = phi(u)`, namely
`y = 2^{-k} phi(u) in <phi(u)> <= phi(Z^3)`.  Hence
`phi(Z[1/2]^3) = phi(Z^3)`, and since `T = Z[1/2]^3 semidirect SL_3(Z)` and
`Gbar = Z^3 semidirect SL_3(Z)` share the `SL_3(Z)` factor,

    phi(T) = phi(Gbar) .

No conjugation by `tau` is used, so the step is available inside `E_T`.

*Step 2: run the level-collapse verbatim.*  Now let `phi` be a homomorphism
from `E_T` to a finite group.  Its restriction to `T` satisfies Step 1, so
`T <= Gbar . ker phi`.  Fix a site `x = g Gbar`; conjugating that inclusion by
`g` and using normality of `ker phi` gives `T <= Stab_V(x) . ker phi`.  Write
`h in T` as `h = sigma k` with `sigma in Stab_V(x)` and `k in ker phi`.  Then

    phi(c_{hx}) = phi(sigma) phi(k c_x k^{-1}) phi(sigma)^{-1}
                = phi(sigma c_x sigma^{-1}) = phi(c_{sigma x}) = phi(c_x) .

This is Theorem 9.1 of the cited note with its input `phi(T) = phi(Gbar)`
supplied by Step 1 instead of by blindness.  `T` is transitive on each level
(translations already are), so the levels are exactly the `T`-orbits of sites,
and therefore all lamps of a common level have the same image.

*Step 3: conclude.*  The marked pair is `a = tau o = (1,[0])` and
`b = v_1 tau o = (1,[e_1])` (`literal-lamp-kernel-clifford-block-amalgam`),
which lie in the same level `1`.  So `phi(c_a) = phi(c_b)` and

    phi(w) = phi([c_a, c_b]) = 1 .

Both `c_a, c_b` and `w` lie in `N_E <= E_T`, and `w != 1` in `E` by
`prop:witness`, hence `w != 1` in `E_T`.  So no finite quotient of `E_T`
separates `w` from the identity, and `E_T` is not residually finite. []

## Why this does not touch Lemma 3.1

Step 1 consumes the whole telescope: `2^{-k}` must be available for every `k`.
A single level `Gamma_n = 2^{-n} Z^3 semidirect SL_3(Z)` has a lattice
translation subgroup, not a 2-divisible one, and `[Gamma_n : Gbar] = 8^n` is
finite, so `Gbar` is separable in `Gamma_n` outright and finite quotients of
`Gamma_n` do separate the levels below `n`.  The collapse is a property of the
union, invisible in any single level — which is precisely why the block
windows `M_J semidirect Gamma_n` of Lemma 3.1 are immune to it, and why the
soficity proof must be local.
