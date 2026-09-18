---
rg: 2
id: hard-self-similar-groups-via-self-similar-kms-modules
kind: route
title: Hard finitely presented self-similar groups from Kharlampovich-Myasnikov-Sapir groups whose configuration modules are self-similar
target: fp-self-similar-groups-with-arbitrarily-hard-word-problem
requires:
  - kms-configuration-modules-carry-self-similar-structures
  - lamp-digit-modules-give-self-similar-semidirect-products
  - kms-arbitrarily-hard-fp-rf-groups
---

Fix a recursive `T`.

1. **Choose the group.** By `kms-configuration-modules-carry-self-similar-structures`,
   pick a machine `M` whose KMS group `G(M) = T ⋊ Q` is harder than `T` in the sense of
   `kms-arbitrarily-hard-fp-rf-groups`. Its top `Q` acts faithfully and self-similarly
   on some `T_X`, and its configuration module carries a self-similar module structure
   `(ρ, λ)` over that action.
2. **Make it self-similar.** Item 2 of
   `lamp-digit-modules-give-self-similar-semidirect-products` gives an injective
   restriction-closed `Q`-map `T → F_p^{X^*}`. Item 1 then realizes `T ⋊ Q` as a
   self-similar subgroup of `Aut(T_{X × F_p})`. KMS construct `G(M)` as a split
   extension of `T` by `Q` (KMS §1, line 374), so this is `G(M)` itself, acting
   faithfully.
3. **Conclude.** `G(M)` is finitely presented by construction, so it is a finitely
   presented self-similar group whose word problem beats `T`. ∎

Combined with `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`, this would
give finitely presented simple groups beyond every recursive bound.

**Dead (09-18, bh-free-25).** Its premise is refuted by
`kms-configuration-modules-have-trivial-coinvariants`: `T = I_Q·T`, so step 1 never
applies. The affine alternative, with the top mixing lamps and positions, is excluded for
hard machines by `affine-self-similar-groups-are-function-field-linear`.
