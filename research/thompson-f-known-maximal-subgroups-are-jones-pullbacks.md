---
rg: 2
id: thompson-f-known-maximal-subgroups-are-jones-pullbacks
kind: claim
title: The explicit non-parabolic maximal subgroups of Thompson's group F of Golan–Sapir and of Golan are preimages of Jones' subgroups under endomorphisms of F, and each Jones subgroup is the stabilizer of a digit-sum colouring
distinct_from:
  jones-subgroup-is-stabilizer-of-odd-digit-sum-dyadics: that imports the case n = 2 (Jones' subgroup stabilizes the odd-digit-sum dyadics); this imports the colouring description of every Jones subgroup F_n and the two constructions of maximal subgroups from them
  jones-subgroup-cosets-form-a-parity-lamplighter: that describes the coset space of the Jones subgroup; this records which maximal subgroups of F are built from Jones subgroups and how
---

**ESTABLISHED (citation).** For `n ≥ 2` and `i ∈ {0, …, n−1}` let `S_i^(n)` be the set of
dyadic fractions in `(0,1)` whose terminating binary expansion has digit sum `≡ i (mod n)`.
Let `c_n : D → ℤ/n` be the digit-sum colouring, `c_n(x) = (number of ones of x) mod n`.
Let `F_{1,n} ≤ F` be the subgroup of elements whose slope at `1^−` is a power of `2^n`.

1. **Jones subgroups are colouring stabilizers.** For every `n ≥ 2`,
   `\vec F_n = ∩_i Stab_F(S_i^(n)) = {g ∈ F : c_n ∘ g^{-1} = c_n}`.
   Here `\vec F_2 = \vec F` is Jones' oriented subgroup.
2. **Golan–Sapir maximal subgroup.** Let `Ψ : F → F_{1,2}` be the isomorphism with
   `x_0 ↦ x_0x_2`, `x_1 ↦ x_1x_2`. Then `H = Ψ^{-1}(\vec F)` is a maximal subgroup of infinite
   index in `F` that fixes no point of `(0,1)`. The only subgroups of `F` containing `\vec F` are
   `\vec F`, `F_{1,2}` and `F`.
3. **Golan's family.** For every prime `p`, the only subgroups of `F` strictly containing
   `\vec F_p` are `F_{1,p}` and `F`. So `\vec F_p` is maximal in `F_{1,p}`, and for an
   isomorphism `ν : F_{1,p} → F` the subgroup `ν(\vec F_p)` is maximal of infinite index in `F`.
   These are pairwise non-isomorphic for different `p`.

Reformulation used downstream. In items 2 and 3 the maximal subgroup has the form
`ψ^{-1}(\vec F_n)` for a homomorphism `ψ : F → F`: take `ψ = Ψ` in item 2, and `ψ = ν^{-1}`
(an isomorphism `F → F_{1,p}` followed by inclusion) in item 3, since `x ∈ ν(\vec F_p)` iff
`ν^{-1}(x) ∈ \vec F_p`.

Proof route: `thompson-f-known-maximal-subgroups-are-jones-pullbacks-citation`.
