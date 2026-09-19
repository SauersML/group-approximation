---
rg: 2
id: sft-leavitt-units-word-problem-computes-sft-language-proof
kind: route
title: Conjugate the letter idempotents into place by the diagonal shift unitaries and multiply them with a balanced tree of elementary commutators in GL_3
target: sft-leavitt-units-word-problem-computes-sft-language
requires: []
---

Lane proof (swarm-0917-w18c-w18c-bh-pull, 2026-09-19). Not independently reviewed. Elementary. The
identity of step 3 and the length bound of step 4 are checked numerically in
`experiments/hard-rigid-sft-leavitt-units-2026-09-17/commutator_tree_check.py` (matrix models of `R`,
`m <= 16` leaves, random idempotent and non-idempotent entries; prints `OK`).

## 1. `GL_3(R) ≅ R^×`

`L` contains `x_1, x_2, y_1, y_2` with `x_i y_j = δ_ij` and `y_1 x_1 + y_2 x_2 = 1`. So `L ≅ L^2` as right
`L`-modules, hence `L ≅ L^3`, and `M_3(L) ≅ End_L(L^3) ≅ End_L(L) ≅ L` as algebras. Tensoring with `B`
gives `M_3(R) ≅ B ⊗ M_3(L) ≅ R`, so `GL_3(R) ≅ R^×`. (This is also item 2 of
`central-simple-leavitt-tensor-unit-groups-are-simple` under its hypotheses; here no hypothesis is
needed.) The isomorphism need not be computable: step 5 uses only that the finitely many elements of `E`
are fixed words in the generators of `Γ`.

## 2. Leaves

For `v ∈ Z^2`, `u_v e_a u_v^(−1) = e_a ∘ (−v)`, and `(e_a ∘ (−v))(x) = ((−v)x)(0) = x(v)`. So
`u_v e_a u_v^(−1) = 1_{x(v) = a}`. As `D_v = diag(u_v, u_v, u_v)` is a scalar matrix,
`D_v (1 + c E_ij) D_v^(−1) = 1 + (u_v c u_v^(−1)) E_ij`. Writing `D_v = D_(1,0)^(v_1) D_(0,1)^(v_2)` as a
word of length `|v|_1`, the word `D_v x_(a,ij) D_(−v)` has length `2|v|_1 + 1` and equals
`1 + 1_{x(v) = a} E_ij` (tensor factor `⊗ 1` suppressed).

## 3. The commutator tree

With `[g, h] = g h g^(−1) h^(−1)`: for distinct `i, j, k` and any `a, b ∈ R`,
`[1 + a E_ij, 1 + b E_jk] = 1 + ab E_ik`. (Expand: `(1 + aE_ij)(1 + bE_jk)(1 − aE_ij)(1 − bE_jk)`; the
only surviving cross term is `ab E_ik`, since `E_ij E_ij`, `E_jk E_jk`, `E_jk E_ij`, `E_ik E_ij` and
`E_ik E_jk` all vanish for distinct `i, j, k`.)

Define `τ(c_1, …, c_m; i, k)` for leaves `c_t` and distinct `i, k ∈ {1, 2, 3}`:
- if `m = 1`, it is the leaf word for `1 + c_1 E_ik`;
- otherwise let `j` be the third index and `h = ⌈m/2⌉`, and put
  `τ = [τ(c_1, …, c_h; i, j), τ(c_(h+1), …, c_m; j, k)]`.

By induction and the identity, `τ = 1 + c_1 c_2 ⋯ c_m E_ik`. No index conversion is ever needed, since
the third index is always free. Inverses of subwords are words over the symmetric set `E` of the same
length.

For `p : F -> A` with `F = [0, n)^2`, take the leaves `c_v = 1_{x(v) = p(v)}` (`v ∈ F`, any order) and
`W(p) = τ(…; 1, 3)`. The `c_v` lie in the commutative algebra `LC(Ω, F_2)`, so their product is
`Π_v 1_{x(v) = p(v)} = 1_[p]`. Hence `W(p) = 1 + (1_[p] ⊗ 1) E_13`.

`W(p) = 1` iff `1_[p] ⊗ 1 = 0` in `R`. The map `b -> b ⊗ 1` from `B` to `B ⊗ L` is injective (tensor over a
field, `L ≠ 0`), and `LC(Ω, F_2) -> B` is injective. So `W(p) = 1` iff `[p] ∩ Ω = ∅`, i.e. iff `p` occurs
in no configuration of `Ω` (by shift invariance, at no position).

## 4. Length

Let `ℓ(m)` be the length of the tree over `m` leaves of length 1: `ℓ(1) = 1` and
`ℓ(m) = 2ℓ(⌈m/2⌉) + 2ℓ(⌊m/2⌋)`. Claim `ℓ(m) <= 2m^2 − 1`. It holds for `m = 1`. For `m = 2t`:
`ℓ(m) <= 4(2t^2 − 1) = 2m^2 − 4`. For `m = 2t + 1`: `ℓ(m) <= 2(2(t+1)^2 − 1) + 2(2t^2 − 1) = 2m^2 − 2`.
With leaves of length at most `λ` the length is at most `(2m^2 − 1)λ`. Here `m = n^2` and
`λ <= 2(2n − 2) + 1 < 4n`, so `|W(p)| < 8 n^5`. The word is written down in time polynomial in `n`.

## 5. Complexity transfer

Fix, for each of the finitely many `g ∈ E`, a word `w_g` for its image in `Γ` over the generators of `Γ`;
let `c = max |w_g|`. On input `p`, write `W(p)`, substitute, and run the word-problem algorithm of `Γ` on
the result, of length `<= 8c n^5`. Answer "admissible" iff the result is not the identity. By step 3 this
is correct. Time: `W(8c n^5)` plus `O(n^6)` for writing and substituting. So the time is at most
`C·W(C n^5) + C n^6 + C`. ∎
