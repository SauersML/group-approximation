---
rg: 2
id: injective-char-p-lamp-realizations-miss-fixed-points
kind: claim
title: "Class-kill for injective char-p Burger lamp realizations in nV: torsion lifts have clopen fixed sets, so an injective realization misses every fixed point of every finite-order affine lift; no conjugacy onto (F_p^2)^Z exists for p >= 3, the linear injective version misses 0 for every p, and for p = 2 a conjugacy needs fixed-point-free torsion"
distinct_from:
  brin-thompson-torsion-has-clopen-fixed-sets: that is the germ statement for torsion in nV, used here as the only input; this transports it through an injective intertwiner to the algebraic side and reads off which realizations of char-p Burger modules die
  char-p-burger-lamp-realizations-refute-haagerup: that is the positive criterion; this kills the injective part of its search space
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that kills block-split Z^2 subgroups through coordinate shadows; this kills injective encodings of an elementary abelian p-module through fixed-point germs of torsion
artifacts:
  - experiments/nv-break-2026-09-17/check_char_p_burger_lamp.py
  - experiments/nv-break-2026-09-17/check_char_p_burger_lamp.out.txt
---

**ESTABLISHED** by `injective-char-p-lamp-realizations-miss-fixed-points-proof`.
- Only input: `brin-thompson-torsion-has-clopen-fixed-sets` (ESTABLISHED).
- Lane proof by swarm-0917-w17-w17-nv-break. Not independently reviewed.

## Setting

- As in `char-p-burger-lamp-realizations-refute-haagerup`: `R = F_p[t,t^-1]`, `M = R^2`, and
  `M^ = (F_p^2)^Z`.
- `φ : C^n → M^` is continuous and affinely spanning, and `Λ ≤ nV`.
- `λ ↦ a_λ(ξ) = q(λ)·ξ + v_λ` is the induced affine action, with `φ∘λ = a_λ∘φ` and
  `q(Λ) ⊇ EL_2(R)`.
- `Y = φ(C^n)`. Call the realization **injective** if `φ` is injective, and **linear** if every
  `v_λ = 0`.

## Theorem K

Assume `φ` is injective.
- **(0) Transport.** If `a_λ` has finite order, then `λ` has finite order, and
  `Fix(λ) = φ^-1(Fix a_λ)` is clopen.
- **(i) Torus, `p ≥ 3`.** Let `c` generate `F_p^×` and `d_c = diag(c, c^-1)`.
  - Every lift `a_λ` of `d_c` has order dividing `p − 1` and exactly one fixed point
    `ξ_c = −(D − 1)^-1 v_λ`, where `D(α, β) = (c^-1 α, c β)`.
  - The point `ξ_c` is **not** in `Y`.
  - In particular `φ` is not surjective: **no conjugacy** of a subgroup of `nV` onto the affine
    `EL_2(R)`-action on `M^` exists for `p ≥ 3`. In the linear case, `0 ∉ Y`.
- **(ii) Shears, every `p`.** Let `λ_1` and `λ_2` lift `e_12(1)` and `e_21(1)`.
  - Their affine lifts always have finite order: `p` for odd `p`, and `2` or `4` for `p = 2`.
  - `Fix(a_λ1) ∩ Fix(a_λ2)` has at most one point.
  - `φ^-1(Fix a_λ1)` and `φ^-1(Fix a_λ2)` are **disjoint** clopen sets.
  - In the linear case both fixed sets contain `0`, so `0 ∉ Y` for every `p`.
- **(iii) Conjugacies for `p = 2`.** If `φ` is surjective, hence a homeomorphism onto `M^`, then
  every finite-order `λ ∈ Λ` with `q(λ) ≠ 1` acts on `C^n` **without fixed points**. Moreover:
  - for `r ≠ 0`, every `λ` with `q(λ) = e_12(r)` has translation `v_λ` with nonzero
    `α`-component, and so acts without fixed points, whatever its order;
  - symmetrically, every lift of `e_21(r)` has nonzero `β`-component.
  - Proposition B's homeomorphism (`p = 2`, `k = 2`) can therefore carry only shear lifts with this
    property. With `v = 0` for all lifts it dies.

## Invariant and death step

- **Invariant:** the fixed-point germ of torsion. A torsion element of `nV` is the identity near
  each of its fixed points.
- **Death step, the same for every member.** Injectivity transports torsion from the algebraic side
  (`a_λ` of finite order) to `nV`. On the algebraic side, the fixed set of a nontrivial torsion
  automorphism of `M^` is a closed coset with **empty interior**: a single point for the torus, or
  a coset of `{α = 0}` for the shear. Its preimage must be clopen, and a clopen set of the perfect
  space `C^n` that sits inside a nowhere-dense or one-point set is empty.

## What survives

- **Non-injective `φ`.** In these, torsion on the algebraic side need not lift to torsion. For
  `κ ∈ ker(λ ↦ a_λ)`, `κ` preserves every fibre of `φ`. So `λ^(ord a_λ)` only has to preserve the
  fibres, and it can have infinite order.
- These are the **lazy / pending-data encodings**: `φ` sums stored data with not-yet-applied
  corrections, and the fibres record how the corrections are split.
- For `p = 2`, conjugacies whose torsion lifts are all fixed-point free (item iii).

## Checks

`experiments/nv-break-2026-09-17/check_char_p_burger_lamp.py` verifies, on finite truncations
(`check_affine_unipotent` and `check_affine_torus`):
- the orders of the affine shear lifts: `{2: 4, 3: 3, 5: 5}` when the `α`-translation is nonzero;
- the torus lifts have order `p − 1` and exactly one fixed point, for `p = 3, 5, 7`.
