---
rg: 2
id: cyclotomic-class-group-counts-zp-actions-on-stable-o2-proof
kind: route
title: Normal form plus Köhler UCT gives KK^G-classes; Meyer realizes them by outer actions; Gabe--Szabó upgrades to cocycle conjugacy
target: cyclotomic-class-group-counts-zp-actions-on-stable-o2
requires: [bootstrap-zp-actions-realize-every-cyclotomic-k-module]
---

**Sources (read 2026-09-12 from text extractions on MSI).**
* Gabe--Szabó, *The dynamical Kirchberg--Phillips theorem*, arXiv:2205.04933.
  Theorem A: "Let G be a countable discrete amenable group and let α : G y A and
  β : G y B be pointwise outer actions on stable Kirchberg algebras.  Then (A,α)
  and (B,β) are cocycle conjugate if and only if they are KK^G-equivalent."
* Meyer--Nadareishvili, arXiv:2604.12529v2, introduction: "It was shown in [7]
  that any KK^G-equivalence class in the equivariant bootstrap class is
  represented by a pointwise outer action on a Kirchberg algebra, still in the
  bootstrap class."  Theorem 2.10 is quoted in
  `bootstrap-zp-actions-realize-every-cyclotomic-k-module-proof`.

**Item 1, injectivity.**  Let `α, α'` be pointwise outer bootstrap actions on
`O_2 ⊗ K` with isomorphic `O`-modules `M ≅ M'`.
- The restriction is `O_2 ⊗ K ≃ 0`, so both invariants are `Q(0, 0, M)`.
- An `O`-isomorphism `M → M'` induces a `K_p`-isomorphism of the normal forms:
  identity pattern on components 1 and 2, commuting with `α_12 = 1 − ϑ` and
  `α_21 = 1`.
- Köhler's UCT (Theorem 2.10, both algebras in `B^G`) lifts it to a
  KK^G-equivalence.
- Gabe--Szabó Theorem A (`G` finite, hence amenable) gives cocycle conjugacy.

Conversely, cocycle conjugacy gives KK^G-equivalence, hence isomorphic
invariants.  A `K_p`-isomorphism restricts on component 1 to an `O`-isomorphism,
since `s_1` acts as `ϑ`.

**Item 1, surjectivity.**  Given `M`, item 2 of the parent claim gives
`A ∈ B^G` with `Res A ≃ 0` and invariant `Q(0, 0, M)`.
- By Meyer's realization, `A` is KK^G-equivalent to a pointwise outer action `β`
  on a Kirchberg algebra `B`.
- Replace `(B, β)` by `(B ⊗ K, β ⊗ id)`.  The KK^G-class is unchanged, and
  pointwise outerness passes to the stabilization (standard; not re-read).
- `B ⊗ K` is a stable Kirchberg algebra with `Res ≃ 0`.  The stable
  Kirchberg--Phillips theorem, KK form, gives `B ⊗ K ≅ O_2 ⊗ K`.

**Item 2.**  `O` is a Dedekind domain, the localization of `Z[ζ_p]` at `p`.
- A finitely generated torsion-free `O`-module of rank one is isomorphic to a
  fractional ideal, and isomorphism classes of these are `Cl(O)`.
- The primes of `Z[ζ_p]` over `p` reduce to `(1 − ζ_p)`, which is principal.
  So the localization sequence `⊕_(𝔭 | p) Z → Cl(Z[ζ_p]) → Cl(O) → 0` gives
  `Cl(O) = Cl(Z[ζ_p]) = Cl(Q(ζ_p))`.
- Every such module arises as `K_0` with `K_1 = 0`, with `ζ_p` acting by
  multiplication, and the modules are pairwise non-isomorphic.

**Item 3.**
- The crossed product of a bootstrap `G`-algebra is KK-equivalent to the crossed
  product of a type I `G`-algebra, so it satisfies the UCT.
- For pointwise outer `α` on the simple purely infinite `O_2 ⊗ K`, the crossed
  product is simple and purely infinite.  Barlak--Li II cite this in the proof of
  their Theorem 4.12; it was not re-read here.  It is nuclear, separable and
  stable.
- Its K-theory is a fractional ideal `𝔞` in degree 0 and `0` in degree 1.  As an
  abelian group `𝔞` is a finitely generated torsion-free `Z[1/p]`-module of rank
  `p − 1`, hence `≅ Z[1/p]^(p−1)`.
- The stable Kirchberg--Phillips theorem with the UCT identifies all of these
  crossed products.
- Baaj--Skandalis duality makes the dual actions KK^Ĝ-equivalent exactly when
  the original actions are KK^G-equivalent, that is, exactly when the ideal
  classes agree.

**Not re-read from source:** stability of pointwise outerness under
stabilization, pure infiniteness of the crossed product, the class number table.
None of these touches the UCT problem.
