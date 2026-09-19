---
rg: 2
id: sft-leavitt-units-word-problem-computes-sft-language
kind: claim
title: The word problem of the units of (LC(Ω, F_2) ⋊ Z^2) ⊗ L_2 decides the n × n pattern language of the Z^2-subshift Ω through nested elementary commutators of length O(n^5)
distinct_from:
  alternating-v-full-group-wp-computes-sft-language: that encodes patterns into the alternating full group of V times Λ ⋉ X by commutators of 3-cycles; this encodes them into GL_3 of a Leavitt tensor of the crossed-product algebra by commutators of elementary matrices, so it applies to a unit group whose finite presentation and simplicity are already proved for quantum rigid shifts.
  leavitt-tensor-unit-word-problem-reduces-to-base: that is the upper bound, from the word problem of the units to the zero test of the coefficient algebra; this is the matching lower bound for crossed-product coefficients, from the pattern language of the subshift to the word problem of the units.
  leavitt-square-units-have-conp-parity-p-complete-word-problem: that pins the complexity for the one coefficient algebra L; this lower-bounds it for every subshift crossed product, with no fixed complexity class.
  full-group-word-problem-iff-recursive-language: that is Grigorchuk--Medynets' decidability equivalence for derived full groups of minimal Z-subshifts; this is a quantitative one-sided reduction for unit groups of Leavitt tensors of Z^2 crossed products.
artifacts:
  - experiments/hard-rigid-sft-leavitt-units-2026-09-17/commutator_tree_check.py
---

**ESTABLISHED (lane proof, swarm-0917-w18c-w18c-bh-pull, 2026-09-19; unreviewed; elementary)** by
`sft-leavitt-units-word-problem-computes-sft-language-proof`.

**Setting.**
- `Ω ⊆ A^(Z^2)` is a nonempty subshift over a finite alphabet `A`, with `(λx)(g) = x(g − λ)`. No finite
  type, minimality or freeness is assumed.
- `B = LC(Ω, F_2) ⋊ Z^2`, with unitaries `u_s` (`s ∈ Z^2`) and `u_s f u_s^(−1) = f ∘ s^(−1)`.
  `L = L_(F_2)(1,2)` and `R = B ⊗ L`.
- For `a ∈ A`, `e_a = 1_{x(0) = a} ∈ LC(Ω, F_2)`.
- In `GL_3(R)`: `x_(a,ij) = 1 + (e_a ⊗ 1) E_ij` for `a ∈ A`, `i ≠ j`, and `D_s = diag(u_s, u_s, u_s)` for
  `s ∈ S = {±(1,0), ±(0,1)}`. Let `E` be this finite set and `Q = <E> ≤ GL_3(R)`.

**Theorem.**
1. `GL_3(R) ≅ R^×`. So `Q` is, up to isomorphism, a finitely generated subgroup of `R^×`.
2. There is an algorithm, running in time polynomial in `n`, with input a pattern `p : [0, n)^2 -> A` and
   output a word `W(p)` over `E` (a symmetric set: `x_(a,ij)^(−1) = x_(a,ij)` and `D_s^(−1) = D_(−s)`) of
   length at most `8 n^5`, such
   that `W(p) = 1 + (1_[p] ⊗ 1) E_13` in `GL_3(R)`. Here `1_[p]` is the indicator of the cylinder of `p`.
   So `W(p) = 1` iff `p` occurs in no configuration of `Ω`.
3. **Complexity transfer.** Let `Γ ⊇ Q` be a finitely generated group, for instance `R^×` when it is
   finitely generated. If the word problem of `Γ` is decidable in time `W(l)`, with `W` nondecreasing,
   then the globally admissible `n × n` patterns of `Ω` are decidable in time `C·W(C n^5) + C n^6 + C`,
   for a constant `C` depending on `Ω` and `Γ`.

**Use.** With `hard-quantum-rigid-free-minimal-z2-sfts-exist` and the Leavitt-tensor host theorems, this
turns hard quantum rigid shifts into finitely presented simple groups with hard word problems (route
`complex-fp-simple-via-hard-rigid-sft-leavitt-units`). Combined with the upper bound
`leavitt-tensor-unit-word-problem-reduces-to-base`, the word problem of `R^×` and the language of `Ω`
agree up to a single-exponential blow-up.

DERIVATION
sft-leavitt-units-word-problem-computes-sft-language-proof
