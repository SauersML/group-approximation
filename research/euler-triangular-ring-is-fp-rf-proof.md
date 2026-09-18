---
rg: 2
id: euler-triangular-ring-is-fp-rf-proof
kind: route
title: Peirce decomposition of the presented ring, and folding the Euler base modulo l^r
target: euler-triangular-ring-is-fp-rf
requires:
  - resolvent-ring-has-path-normal-form
  - resolvent-presentation-ring-is-residually-finite
---

Notation as in the target. `D` is the ring presented by `u, x, x', B` and the four `D`-relations
(Step 1 of `resolvent-ring-has-path-normal-form-proof`).

**1. Finite presentation.** Let `R'` be the presented ring and `1 - e` the complementary idempotent.
- *Where the generators live.* Every generator `g` satisfies `g = e g`: for the `D`-generators by
  `g = e g e`, and for `m` by `e m = m`. So `(1-e) g = 0`, and `(1-e) R' = Z(1-e)`.
- *Words through `m`.* Since `m = m(1-e)`, any word with a generator after `m` vanishes. So
  `e R' e` is the image `D'` of `D`, and `e R' (1-e) = D' m`.
- *The Peirce decomposition.* `R' = D' ⊕ D' m ⊕ Z(1-e)`.
- *Comparison.* The assignment in the target respects every relation, since `u v_0 = 0` in `M`. So
  it gives a surjection `R' -> T_l`, which maps:
  - `D'` onto `D`;
  - `D' m` onto `M = D v_0`;
  - `Z(1-e)` onto `Z`.
- *Injectivity.* `D' -> D` is an isomorphism, because `D'` is a quotient of `D`. `D' m` is a quotient
  of `D/Du`, since the only relation on `m` is `u m = 0`, and `D/Du -> M` is the identity. So all
  three pieces map isomorphically, and `R' ≅ T_l`.

**2. Residual finiteness.**
- *The folding maps.* `M -> M_(r,N)`, `f_j -> f_(j mod N)` with coefficients reduced mod `l^r`, is
  `D`-linear. `u` acts on `f_j` by `lj` in both, and `lj mod l^r` depends only on `j mod l^(r-1)`.
  `x` shifts in both. `B` acts by `(1+lj)^(-1)` in both.
- *The ring maps.* The map `[[d, n],[0, k]] -> [[ρ(d), n̄],[0, k mod l^r]]`, with `ρ : D -> End(M_(r,N))`
  the action, is a ring homomorphism onto a subring of a finite ring. The product rule
  `[[dd', dn' + n k'],[0, kk']]` is preserved because the fold is `D`-linear and `Z`-linear.
- *Separating points.* Let `t = [[d, n],[0, k]] != 0`.
  - If `k != 0`, take `r` with `k ∉ l^r Z`.
  - If `d != 0`, some `ρ(d)` is nonzero for suitable `(r, N)`. This is the case "δ != 0" of
    `resolvent-presentation-ring-is-residually-finite-proof`: its modules with `E = 0`, `d = 1` and
    `g = 1` are exactly the `M_(r,N)`.
  - If `n != 0`, take `N` larger than the spread of the support of `n` and `r` with some coefficient
    `∉ l^r Z_(l)`.

**3 and 4.**
- `Z_(l) f_0 ⊆ M` by definition.
- `[[h, n],[0,1]]` is a unit of `T_l` for `h in D^×`, with inverse `[[h^(-1), -h^(-1) n],[0, 1]]`.
- With `h in <x, 1+u>` acting on `M` as in `z-localized-embeds-in-fg-rf-soluble-group`, these units
  multiply as `M ⋊ <x, β>`. There `1+u` acts by `1+lj = β`, and `<x, 1+u> ≅ Z≀Z` in its faithful
  action on `M`. ∎
