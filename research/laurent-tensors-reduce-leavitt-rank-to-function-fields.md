---
rg: 2
id: laurent-tensors-reduce-leavitt-rank-to-function-fields
kind: claim
title: A commutative domain of transcendence degree s+m in A ⊗ R, with R central of degree s, forces a polynomial ring in m variables in A ⊗ Frac(R); so Z^4 embeddings through the equicontinuous factor of Ω need two commuting independent elements in the Leavitt algebra over F_2(x,y)
distinct_from:
  leavitt-commuting-units-are-algebraically-dependent: that asks about commuting units of L_(F_2)(1,2) itself; this proves that every embedding of F_2[Z^4] supported on the lattice or an equicontinuous factor forces the polynomial version of that question over the function field F_2(x,y). The two questions are linked only one way.
  algebraic-core-gradings-bound-homogeneous-laurent-rank: that kills subalgebras that are locally matrices over commutative rings; this handles L_2 ⊗ F[Z^s], which is locally matrices over the noncommutative L_2, by passing to the fraction field of the central Laurent ring.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that is the fork question for the whole host; this reduces one sub-mechanism of it (embeddings supported on (LC(Y) ⋊ Z^2) ⊗ L_2 for an equicontinuous factor Y, which contains mechanism (i)) to a single field-uniform Leavitt question.
---

**ESTABLISHED (unreviewed)** (proof: `laurent-tensors-reduce-leavitt-rank-to-function-fields-proof`).
Novelty not searched.

## Statement

Let `F` be a field. Let `A` be an `F`-algebra. Let `R` be a commutative `F`-domain whose fraction field `K` has
`trdeg_F K = s < ∞`. Put `R` in the centre of `A ⊗_F R`.

- **(a) Descent to the fraction field.** Suppose `A ⊗ R` contains a commutative domain `D` (unital or not) with
  `trdeg_F Frac(D) >= s + m`. Then `A ⊗_F K` contains commuting elements `c_1, …, c_m` that are algebraically
  independent over `K`. In other words, the unital `K`-algebra `K[c_1, …, c_m]` is a polynomial ring.
- **(b) Converse for polynomial rings.** Suppose `A ⊗ K` contains commuting elements `c_1, …, c_m` that are
  algebraically independent over `K`. Then `A ⊗ R` contains `R[X_1, …, X_m]`. So if `R ⊇ F[x_1, …, x_s]`
  (for example `R = F[Z^s]`), then `A ⊗ R` contains a polynomial ring over `F` in `s + m` variables.

Write `Q_m(K)` for the statement that `L_K(1,2)` contains `m` commuting elements algebraically independent over
`K`.

- **(c) Laurent tower.** Take `A = L_F(1,2)` and `R = F[Z^s]`. The following hold.
  - If `F[Z^(s+2)]`, or any commutative domain of transcendence degree `s + 2`, embeds in `L_F(1,2) ⊗ F[Z^s]`,
    then `Q_2(F(x_1, …, x_s))` holds.
  - `L_F(1,2) ⊗ F[x_1, …, x_s]` contains a polynomial ring in `s + 2` variables if and only if
    `Q_2(F(x_1, …, x_s))` holds.
- **(d) Field reduction.**
  - If `Q_m(F)` holds, then `Q_m(K)` holds for every field `K ⊇ F`.
  - If `Q_m(K)` holds for some field `K` of characteristic `p`, then `Q_m(F_p(x_1, …, x_e))` holds for some
    finite `e`.
  - So `Q_2` fails for every field of characteristic 2 if and only if, for every `s`, the ring
    `L_(F_2)(1,2) ⊗ F_2[x_1, …, x_s]` contains no polynomial ring in `s + 2` variables.
- **(e) Application to the `Z^4` fork.** Let `Ω` be any minimal `Z^2`-Cantor system. Let `Y` be a totally
  disconnected equicontinuous factor of `Ω`: a point, a finite orbit `Z^2/Λ`, or an odometer
  `lim Z^2/Λ_n`. Put
  `H_Y = (LC(Y, F_2) ⋊ Z^2) ⊗ L_(F_2)(1,2) ⊆ B_Ω ⊗ L_(F_2)(1,2)`.
  - If `F_2[Z^4]` embeds in `H_Y`, then `Q_2(F_2(x, y))` holds.
  - `H_Y` contains `F_2[Z^2]_lattice ⊗ L_2`. So mechanism (i) of the fork (a Laurent pair in a corner of
    `L_2`) is one instance, and so is every "entangled" embedding that uses only the lattice units, functions
    pulled back from `Y`, and `L_2`.

## Why it matters

Take the host in its binary-Leavitt form, `B_Ω ⊗ L_(F_2)(1,2)`. By
`boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts` this is equivalent for group algebras. The fork
`f2-z4-embeds-in-z2-sft-boundary-product-hosts` now decomposes into three prerequisites for NO, each of which can
fail separately:

1. `F_2[Z^3]` does not embed in `B_Ω`. This is mechanism (ii). The w14-bh-pull lane claim
   `steinberg-ore-domains-have-faithful-point-columns`, which is not in this tree, kills it for virtually nilpotent
   acting groups.
2. `Q_2(F_2(x, y))` fails. By (e) this kills every embedding supported on an equicontinuous factor, mechanism (i)
   included.
   - By (d), a failure of `Q_2(F_2(x, y))` also gives the polynomial form of
     `leavitt-commuting-units-are-algebraically-dependent`.
   - The Ara–Cortiñas firewall moves to `K`. A unital map `L_K ⊗ L_K -> L_K` gives `Q_2(K)` through
     `s_0 ⊗ 1` and `1 ⊗ s_0`.
3. Every embedding uses the expansive (non-equicontinuous) part of `Ω` in an essential way. This is mechanism
   (iii-b), and it is the only part left untouched.

Proofs of (1) and (2) must be field-uniform in the following sense. Any argument that shows "no two commuting
independent elements in `L_k(1,2)`" for *every* field `k`, like the centraliser lemma of the w15-bh-pull lane
("`C(s_w) = k[s_u]` over any field"), transfers through (a) and (c) to all of `L_2 ⊗ F[Z^s]` at once.

For the commutative-rank conjecture of the fork, (c) and (d) reduce every instance `L_2 ⊗ F[Z^s]` (a
`Z^(s+1)`-cocycle with AF kernel), at the polynomial level, to the single base instance `s = 0` over function
fields.

## Scope

- (a) needs `R` central. It says nothing about the lattice units of `B_Ω`, which do not commute with `LC(Ω)`.
  That is why (e) is restricted to `H_Y`.
- The converse (b) is for polynomial rings only. Clearing denominators destroys invertibility, so a Laurent pair
  over `K` does not return a Laurent ring `F[Z^(s+2)]` in `A ⊗ F[Z^s]`.
