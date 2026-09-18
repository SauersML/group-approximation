---
rg: 2
id: binary-free-algebra-linear-group-nonexact
kind: claim
title: Some finitely generated subgroup of GL_n over the free algebra F_2<x,y> is not exact
distinct_from:
  fp-simple-nonexact-group: that asks for a finitely presented simple non-exact group; this asks only for a finitely generated non-exact linear group over one free algebra, which by char-two-laurent-linear-groups-satisfy-boone-higman would make the finitely presented simple group L_{F_2}(1,2)^x non-exact.
  decidable-residually-finite-non-exact-group-exists: that is Osajda's graphical small cancellation witness, which is residually finite with decidable word problem but is not known to be linear over any ring; this asks for non-exactness inside one explicit family of linear groups over a noncommutative ring.
  commutative-ring-linear-groups-have-property-a: that is the Guentner--Higson--Weinberger theorem that linear groups over commutative rings, fields included, are exact; this asks whether that theorem fails once the ring is the free algebra, the first noncommutative ring that Leavitt hosts contain.
  elementary-group-property-t-over-free-algebras: that proves property (T) for EL_3(F_2<x,y>); this asks for the failure of exactness, which property (T) does not decide either way.
---

**OPEN.** There are `n ≥ 1` and a finitely generated subgroup
`Γ ≤ GL_n(F_2<x,y>)` that is not exact.

The concrete test case is **`Γ = EL_3(F_2<x,y>)`**.

## Why this matters

By `char-two-laurent-linear-groups-satisfy-boone-higman`, every finitely
generated subgroup of `GL_n(F_2<x,y>)` embeds in `L^x = L_{F_2}(1,2)^x`. That
group is finitely presented and simple (`fp-simple-nonsofic-group`).
Exactness passes to subgroups (`exact-groups-are-closed-under-extensions`). So
this claim implies `fp-simple-nonexact-group`, unconditionally and with no
appeal to Boone--Higman. The route is
`fp-simple-nonexact-group-via-free-algebra-linear-groups`.

By `haagerup-hosts-carry-no-weak-expander`, `L^x` is at present the only
finitely presented simple host in this graph that is known not to be Haagerup.
It is therefore the only one in which an expander-type witness is not already
excluded.

## What is known about the family

- **`n = 1`.** `GL_1(F_2<x,y>) = {1}`, because the free algebra is a domain
  whose only units are scalars. Nothing to find.
- **Linear over a commutative ring.** Every finitely generated subgroup is
  exact, by `commutative-ring-linear-groups-have-property-a`. The candidate
  must use noncommutativity in an essential way.
- **Residual finiteness.** Every finitely generated `Γ` here is residually
  finite. The free algebra over a finite field is residually finite
  dimensional, so `Γ` embeds in a product of `GL_N(F_2)`. So Osajda's
  mechanism (arXiv:1703.03791, Main Theorem: "There exist finitely generated
  residually finite non-exact groups defined by infinite graphical small
  cancellation presentations") is compatible with the family, and residual
  finiteness is no obstruction.
- **Box spaces are a false signal.** Property (T) makes every box space of
  `Γ` an expander, built from its finite quotients `EL_3(A_i)`. It is tempting
  to read that as evidence of non-exactness. It is not. A box space has
  property A exactly when the group is amenable (Roe), not when it is exact.
  The Kazhdan expander is a quotient family of `Γ`, not a subspace of `Γ`.
  `SL_3(Z)` is Kazhdan and exact and has the same expander box spaces. This
  heuristic predicts nothing, and it is recorded so that it is not tried
  again.
- **`n = 2`.** Plausibly exact, through a Cohn--Nagao-type amalgam
  decomposition of `GL_2` over a free algebra. This is unverified.

## Attempts

1. **Weakly embedded expander inside `EL_3(F_2<x,y>)`.** *Untested.* The
   lemma in `haagerup-hosts-carry-no-weak-expander-proof` §2 uses only a
   coarse embedding of `M` into Hilbert space. Exactness gives such an
   embedding, so a weakly embedded expander in `Γ` would make `Γ` non-exact.

   The natural expanders are the Cayley graphs `X_k` of the finite quotients
   `EL_3(A_k)`, with the images of the Kazhdan generators. The reduction map
   `Γ → EL_3(A_k)` goes the wrong way. What is needed is a map
   `X_k → Γ`, uniformly Lipschitz on edges and with fibres of size
   `o(|X_k|)`. No such section is known.

   The obstruction to watch is the one that holds for `SL_3(Z)`. There, the
   known exactness says every such section must fail, and a proposed section
   for `EL_3(F_2<x,y>)` must break that pattern.
