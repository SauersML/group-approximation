---
rg: 2
id: euler-base-embeds-in-fp-steinberg-group
kind: claim
title: The Euler base M ⊇ Z_(l) embeds in the finitely presented group St_N(T_l) for N >= 5, and G_l embeds in the finitely generated residually finite group E_N(T_l)
distinct_from:
  z-localized-embeds-in-fp-kazhdan-steinberg-group: that embeds Z_(l) in St_N(R_l), where Z_(l) is a corner ring and its tame symbols obstruct every quotient; this embeds the whole Euler base in St_N(T_l), where Z_(l) is only a square-zero bimodule.
  euler-base-annihilator-over-lamplighter-is-not-fg: that shows no group ring of an overgroup of Z≀Z presents the Euler base finitely; here elementary matrices carry the D-action through the Steinberg commutator relations, so finitely many relators suffice.
---

**ESTABLISHED** through `euler-base-embeds-in-fp-steinberg-group-proof`. Lane proof, not independently
reviewed. The finite presentation is the refereed rank-five node; no literature input is used.

**Statement.** Let `l` be a prime and `N >= 5`.
1. `St_N(T_l)` is finitely presented.
2. `n -> x_12(ι(n))`, with `ι(n) = [[0, n],[0, 0]] in T_l`, is an injective homomorphism
   `(M, +) -> St_N(T_l)`. In particular `(Z_(l), +)` embeds in `St_N(T_l)`.
3. `E_N(T_l) <= GL_N(T_l)` is finitely generated and residually finite. It contains `ι(M)` as
   `e_12(ι(M))`, and it contains the Euler lamplighter `G_l` through `g -> diag(g, g^(-1), 1, ..., 1)`
   (Whitehead).

**Reading for the bottleneck.** This is the "finitely presented host containing the Euler base" asked for
after `euler-base-annihilator-over-lamplighter-is-not-fg`, realized by a Steinberg group instead of a
metabelian top.
- *The lever.* `[x_(ij)(d), x_(jk)(ι(n))] = x_(ik)(ι(dn))` lets every element `d in D` act on `M`, and
  the Euler relation is a relation of the finitely presented ring `D`.
- *So residual finiteness is the whole question.* `z-localized-embeds-in-fp-rf-group` follows from
  `euler-triangular-steinberg-rf-residual-is-fng`, by route
  `z-localized-fp-rf-via-euler-triangular-steinberg`.
- *No known obstruction.* The corner-symbol obstruction for `R_l`
  (`resolvent-ring-corner-symbols-survive-in-k2`) has no analogue here. `Z_(l)` is not a subring of any
  corner of `T_l`, and the only units are `D^×` and `±1`, up to the unipotent `M`-part.
