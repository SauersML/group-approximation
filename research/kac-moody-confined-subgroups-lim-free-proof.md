---
rg: 2
id: kac-moody-confined-subgroups-lim-free-proof
kind: route
title: Apply the full-limit-set theorem to Rybak's action, then Rybak's MIF criterion to the confined subgroup
target: kac-moody-lattice-confined-subgroups-are-lim-free-and-mif
requires:
  - confined-subgroups-of-lim-free-actions-have-full-limit-set
  - fp-simple-kac-moody-lattices-are-lim-free
  - rybak-general-type-limit-set-topologically-free-iff-mif
---

Let `G`, `S` and `H` be as in the target.

**(1)** By `fp-simple-kac-moody-lattices-are-lim-free`, `G` acts on `S` with general
type and its action on `Λ_S(G)` is topologically free. By
`confined-subgroups-of-lim-free-actions-have-full-limit-set`, `H` acts with general
type, `Λ_S(H) = Λ_S(G)`, and `H` acts on it topologically freely and minimally.

**(2)** The limit set is infinite, so topological freeness gives faithfulness: an
element acting trivially would fix all of `Λ_S(H)`, which has nonempty interior. Then
`H` meets the hypotheses of `rybak-general-type-limit-set-topologically-free-iff-mif`
(general type, faithful on the limit set, topologically free there), so `H` is MIF.

**(3)** Each property follows from MIF.
- **No identity.** A nontrivial `w ∈ F_n` is a nontrivial element of `H * F_n`, so an
  identity of `H` would be a mixed identity.
- **Trivial centralizers.** Let `N ⊴ H` be nontrivial with `1 ≠ c ∈ C_H(N)`, and
  `1 ≠ n ∈ N`. Put `w = [c, x n x^{-1}] ∈ H * ⟨x⟩`, the reduced word
  `c·x·n·x^{-1}·c^{-1}·x·n^{-1}·x^{-1}`, which is nontrivial. For every `g ∈ H`,
  `gng^{-1} ∈ N` commutes with `c`, so `w(g) = 1`, a nontrivial mixed identity.
- **Not partially finitary.** Suppose `H ≤ Sym(Ω)` with image containing `Alt_f(Ω)`
  (LBMB §2.3). Let `σ ∈ H` be a 3-cycle and `w = [σ, xσx^{-1}]^{60}`.
  - `[σ, xσx^{-1}]` is a cyclically reduced word of length 8 in `H * ⟨x⟩`, so it has
    infinite order and `w ≠ 1`.
  - For `g ∈ H`, `gσg^{-1}` is a 3-cycle, so `[σ, gσg^{-1}]` is supported on at most 6
    points. It lies in a copy of `Sym(6)`, whose exponent is 60, so `w(g) = 1`.

  So a partially finitary group is not MIF.

**(4)** `H` acts with general type, so ping-pong on two loxodromic elements with
disjoint fixed points gives a nonabelian free subgroup (Rybak l.164, citing Gromov
8.2.F and Hamann Theorem 2.7; standard, not re-read). Every finite group is a quotient
of some `F_k`, and `F_k ≤ F_2`, so it is a subquotient of `H`.

**(5)** This is the Remark after Step 3 of
`lim-free-confined-subgroups-full-limit-set-proof`, applied to `G ↷ S`. Point
stabilizers of `X_D` have a fixed point in `S`, since the injective hull embedding is
`Isom(X_D)`-equivariant (Rybak l.1555, quoting PSZ Proposition N). ∎
