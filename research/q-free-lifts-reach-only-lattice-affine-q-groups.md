---
rg: 2
id: q-free-lifts-reach-only-lattice-affine-q-groups
kind: claim
title: A dilated copy of Q survives no normal series with Q-free or central factors, and Q^n x| Gamma is Q-free-by-Q-free exactly when Gamma fixes a line-free full-rank subgroup of Q^n
distinct_from:
  lifts-add-no-unipotent-divisibility: that fixes the three-step shape Q-free, central, Q-free and includes U_3(Q); this allows every finite normal series whose factors are Q-free or central, excludes Aff(Q) and B_2(Q) through a dilation, and shows U_3(Q) is not excluded by Q-free towers.
  extension-product-closures-cannot-create-sl-n-q: that closes the class without SL_n(Q) or PSL_n(Q) under extensions, which says nothing about the solvable groups Aff(Q) and B_2(Q); this handles those through a dilation, for towers whose factors are Q-free or central.
  adelic-deck-lifts-exclude-affine-q-n-and-fp-bases: that treats the covering with deck group Q^n; this treats deck groups and bases that contain no Q, and gives the exact affine ceiling there.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this bounds what covering-lift and extension-tower constructions can reach.
---

**ESTABLISHED** through `q-free-lifts-reach-only-lattice-affine-q-groups-proof`.
Not independently reviewed. The arguments are elementary and no priority is
claimed. `Q-free` means "contains no subgroup isomorphic to `(Q,+)`".

## Statement

**(A) Dilation obstruction.** Let `E` have normal subgroups
`1 = N_0 <= N_1 <= ... <= N_k = E` such that each factor `N_i/N_{i-1}` is
Q-free or central in `E/N_{i-1}`. Let `D <= E` with `D ~ (Q,+)`, and let
`S <= Aut(D) = Q^x` be the automorphisms induced by some subset of `N_E(D)`.
If `S != 1`, then `D` has an `S`-invariant subgroup other than `0` and `D`.

So no such `E` contains any of `Aff(Q) = Q x| Q^x`, the Borel group `B_2(Q)`,
or `GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)`, `PSL_n(Q)` for `n >= 2`. In `Aff(Q)`, the
dilations act on the translations through all of `Q^x`. In `SL_2(Q)`,
`diag(a, a^-1)` acts on `[[1,b],[0,1]]` through the nonzero squares. For both
groups `S`, the only invariant subgroups are `0` and `Q`.

**(B) Affine ceiling.** Let `n >= 1`, `Gamma <= GL_n(Q)` and
`H = Q^n x| Gamma` with the standard action. The following are equivalent.
1. `H` embeds in a group `E` with a normal subgroup `N` such that `N` and
   `E/N` are Q-free.
2. `H` has a normal subgroup `M` such that `M` and `H/M` are Q-free.
3. `Gamma` preserves a subgroup `L <= Q^n` of rank `n` that contains no
   rational line `Qv`, `v != 0`.

If in (1) the group `N` is finitely generated abelian, for example the deck group
`Z^m` of a covering, then `L` can be taken to be a lattice, so `Gamma` is
conjugate into `GL_n(Z)`.

- **Satisfy (3):** `Q^n x| GL_n(Z)`; `Q^n x| GL_n(Z[1/m])` with
  `L = Z[1/m]^n`; `Q^n x| GL_n(Z_(q))` with `L = Z_(q)^n`, the localization at
  one prime `q`.
- **Fail (3):** every `Gamma` that contains a copy of `(Q,+)`, since such a copy
  is unipotent and forces a line into `L`. In particular `GL_n(Q)` and
  `SL_n(Q)` (`n >= 2`) fail, and so does `Q^x` for `n = 1`, which gives `Aff(Q)`.

**(C) Sharpness.** Without a dilation, towers of Q-free factors do reach
divisible groups.
- `U_3(Q)` has the normal series `e_13(Z) < {(a,b,c) : a,b in Z, c in Q} < U_3(Q)`.
  Its factors are `Z`, `Z^2 x Q/Z` and `(Q/Z)^2`, all Q-free.
- `Q^n x| GL_n(Z)` has the series `Z^n < Q^n < Q^n x| GL_n(Z)`. Its factors
  are `Z^n`, `(Q/Z)^n` and `GL_n(Z)`, all Q-free.
- So `lifts-add-no-unipotent-divisibility` excludes `U_3(Q)` only because of
  its shape: one Q-free step, one central step, then a Q-free base. A tower of
  two Q-free lifts is not excluded for `U_3(Q)`.
- Every nilpotent group has a central series, so the central option in (A) is
  harmless for nilpotent groups. The dilation is what (A) uses.

## Consequences for the root

- **Torus lifts.** Take the lift group through `R^n -> T^n`, with deck group
  `Z^n` and a Q-free group on the base. By (B), the affine groups `Q^n x| Gamma`
  it can contain have `Gamma` conjugate into `GL_n(Z)`. By (A), and by
  `extension-product-closures-cannot-create-sl-n-q` for every base, it
  contains no `GL_n(Q)`, `SL_n(Q)`, `Aff(Q)` or `B_2(Q)`. So the lift family
  targeted by lane `gq-tbar-lift-n` cannot reach `gl-n-q-embeds-in-fp-simple-group`,
  nor its stepping stones `Aff(Q)` and `B_2(Q)`, through any finite tower of
  Q-free covers and central extensions.
- **What such lifts can still carry** is `Q^n x| GL_n(Z)`: it is the full lift
  of the torsion affine group `(Q/Z)^n x| GL_n(Z)` of `T^n`. This is not
  claimed here; see Attempts.

## Attempts

1. **Torus analogue of `Q <= T-bar` (open, not pursued further).** Suppose a
   finitely presented `W <= Homeo(T^n)` contains the affine group
   `(Q/Z)^n x| GL_n(Z)` (rational translations and linear automorphisms). Then
   the group `W~` of all lifts to `R^n` is an extension of `W` by `Z^n`.
   - `W~` is finitely presented (P. Hall: extensions of finitely presented
     groups by finitely presented groups are finitely presented).
   - `W~` contains `Q^n x| GL_n(Z)` as the lifts of that affine group.
   - For `n = 1`, without the `GL_1(Z) = {±1}` part, this is the mechanism of
     Belk--Hyde--Matucci's `Q <= T-bar`.

   No such `W` is known for `n >= 2`.
   - Products of copies of `T` acting on coordinate circles contain conjugated
     rotation groups. Shears do not normalize them.
   - Dyadic piecewise-affine maps of `T^n` supply only the dyadic rotations
     `(Z[1/2]/Z)^n`.

   The result would have exponentially distorted cyclic subgroups for `n >= 2`,
   from `Z^2 x| SL_2(Z)`, so it would lie outside `VA` (root, O4). By (A) and
   (B) it does not lead to the root, so the lane stopped here.
2. **Adelic lifts (spark S1 of `gq-gq-solenoid-adelic-models.md`).** `GL_n(Q)`
   already acts on the base `(A/Q)^n`, so the lift adds no divisibility. The
   deck-`Q^n` case is closed by `adelic-deck-lifts-exclude-affine-q-n-and-fp-bases`.
