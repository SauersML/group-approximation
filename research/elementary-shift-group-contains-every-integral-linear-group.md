---
rg: 2
id: elementary-shift-group-contains-every-integral-linear-group
kind: claim
title: The three-generated group E(Z) x| Z, finitary integer matrices extended by the shift, contains every integral linear group and lies in E_4 of the Toeplitz ring
requires:
  - sl3z-finite-index-subgroups-are-congruence-subgroups
distinct_from:
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that is an unconditional common simple host for the groups in some nV; this is a single explicit finitely generated group containing every subgroup of every GL_n(Z), whose own Boone-Higman property is open.
  gl-n-q-all-n-in-st-10-of-resolvent-ring: that puts every GL_n(Q) in one finitely presented group St_10(R_L); this is the integral analogue, smaller and without Q.
---

**ESTABLISHED** (lane proof, not reviewed). Items 1–3 are folklore-level; no priority
claimed. The Toeplitz embedding in item 4 is the standard unitary dilation of an
isometry.

Let `e_k` (`k ∈ Z`) be the standard basis of `Z^(Z)`. Let `t` be the shift
`e_k ↦ e_{k+1}`, and `x = e_{01}`, `y = e_{10}` the elementary transvections
`e_1 ↦ e_1 + e_0` and `e_0 ↦ e_0 + e_1` (identity on the other basis vectors). Put
`Σ = ⟨t, x, y⟩ ≤ Aut(Z^(Z))`, and let `E(Z) = ⋃_n E_n(Z)` be the finitary elementary
group (finitary `SL(Z)`).

1. **Structure.** `Σ = E(Z) ⋊ ⟨t⟩`, and `Σ` has solvable word problem.
2. **Universality.** For every `n`, `GL_n(Z)` embeds in `Σ`. Hence `Σ` contains every
   finitely generated subgroup of every `GL_n(Z)`: every polycyclic group
   (Auslander–Swan), every finitely generated nilpotent group, every finite group,
   every finitely generated virtually special group (so every RAAG, finitely
   generated Coxeter group and cubulated hyperbolic group), and, by restriction of
   scalars, every finitely generated subgroup of `GL_n(O_K)` for a number ring `O_K`.
3. **Neither linear nor residually finite.**
   - `Σ` embeds in no `GL_d(K)`, for any field `K` and any `d`: it contains `UT_n(Z)`
     for every `n`, whose derived length tends to infinity, while solvable subgroups
     of `GL_d(K)` have derived length bounded in terms of `d` (Zassenhaus–Mal'cev).
   - `E(Z)` has no nontrivial finite quotient, so every finite quotient of `Σ` is
     cyclic and `Σ` is not residually finite. In particular the self-similar and
     linear Boone–Higman routes cannot reach `Σ` itself.
4. **Toeplitz model.** Let `T = Z⟨s, s* | s*s = 1⟩` (the Toeplitz, or Jacobson, ring,
   one relator). Then `Σ` embeds in `E_4(T)`.

**Consequence.** If `Σ` satisfies Boone–Higman, one finitely presented simple group
contains every integral linear group: route
`integral-linear-one-host-via-elementary-shift-group` into
`one-fp-simple-group-contains-every-integral-linear-group`.

## Proof

**1.** `t^k x t^{-k} = e_{k,k+1}` and `t^k y t^{-k} = e_{k+1,k}`. Adjacent elementary
transvections generate every elementary transvection on an interval of indices
(`[e_{ij}, e_{jl}] = e_{il}` for distinct `i, j, l`), hence `E_n(Z) = SL_n(Z)` on every
interval. So `E(Z) ≤ Σ`. `t` normalizes `E(Z)` and no nonzero power of `t` is
finitary, so `Σ = E(Z) ⋊ ⟨t⟩`. A word evaluates to a pair (finitary integer matrix,
exponent of `t`), computed exactly; it is trivial iff the exponent is `0` and the
matrix is the identity.

**2.** `g ↦ diag(g, det g^{-1})` embeds `GL_n(Z)` in `SL_{n+1}(Z)`, which is `E(Z)` on the
indices `0, …, n`. The listed classes are integral linear by the cited classical
theorems (Auslander–Swan for polycyclic; finite groups by permutation matrices;
virtually special groups lie virtually in RAAGs, which are `Z`-linear, and induction
gives a `Z`-linear representation of the whole group).

**3.** `UT_n(Z) ≤ SL_n(Z) ≤ Σ` has derived length `⌈log_2 n⌉`. For finite quotients:
let `N ⊴ E(Z)` have finite index `m`. For `n ≥ 3`, `N ∩ SL_n(Z)` has index `≤ m`, so it
is a congruence subgroup (`sl3z-finite-index-subgroups-are-congruence-subgroups`,
Bass–Milnor–Serre and Mennicke), and `SL_n(Z)/(N ∩ SL_n(Z))` is a quotient of some
`SL_n(Z/q)`, a perfect group. A nontrivial quotient of `SL_n(Z/q)` has a quotient
`PSL_n(F_p)` for a prime `p | q`, of order larger than `m` once `n` is large. So
`SL_n(Z) ≤ N` for all large `n`, hence `N = E(Z)`.

**4.** `T` acts faithfully on `Z^(N)` by `s: e_n ↦ e_{n+1}`, `s*: e_n ↦ e_{n−1}`,
`e_0 ↦ 0` (the words `s^i s*^j` form a `Z`-basis of `T` and act by linearly
independent operators). So `M_2(T)` acts faithfully on `Z^(N) ⊕ Z^(N)`; identify the
first copy with the indices `k ≥ 0` and the second with `k < 0`.
- `u = [[s, 1−ss*],[0, s*]]` is invertible with inverse `[[s*, 0],[1−ss*, s]]` (use
  `s*s = 1`), and it acts as the bilateral shift `t`.
- The matrix units of `M_2(T)` built from `s^i(1−ss*)s*^j` realize every finitary
  integer matrix, so `E(Z) ≤ GL_2(T)` and `Σ = ⟨u⟩ ⋉ E(Z) ≤ GL_2(T)`.
- Each finitary transvection is `1 + ab` with `a` a diagonal matrix unit and `b` an
  off-diagonal one, so `ba = 0`. Then `diag(1+ab, 1) = e_{12}(a) e_{21}(b) e_{12}(−a) e_{21}(−b)`
  in block form, so `diag(1+ab, 1) ∈ E_4(T)`. By Whitehead's lemma `diag(u, u^{-1}) ∈ E_4(T)`.
- `σ ↦ diag(σ, π(σ))`, where `π: Σ → GL_2(T)` kills `E(Z)` and sends `u ↦ u^{-1}`, is an
  injective homomorphism `Σ → GL_4(T)` whose generators land in `E_4(T)`. ∎
