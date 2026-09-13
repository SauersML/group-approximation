---
rg: 2
id: pbh-free-action-via-relative-automorphisms-proof
kind: route
title: Put the input in a finitely presented simple MIF group by Theorem C, embed that group in its relative automorphism actor by right translations of x_1, and read off freeness
target: pbh-groups-act-freely-in-relative-automorphism-actors
requires:
  - type-a-action-gives-boone-higman-for-subgroups
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

Direct proof (2026-09-13, lane `solve-bh-free-solvable`). Not independently reviewed.
Sources were read 2026-09-13 in the extracted text of arXiv:2503.21882v2 on MSI
(`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`).

Let `G ≤ E`, where `E` admits an action of type (A).

**1. A simple MIF overgroup.**
- `E` is finitely presented, hence finitely generated.
- By `type-a-action-gives-boone-higman-for-subgroups` (Zaremsky, Corollary B),
  applied to `E ≤ E`, it has solvable word problem.
- By BFFHZ Theorem C, (i) implies (iv) (`fp-simple-highly-transitive-groups-satisfy-pbh`),
  `E` embeds in a finitely presented simple MIF group `M`. Identify `G ≤ E ≤ M`.

**2. The actor.** `Γ = Aut_M(M * F_2)` acts on `S = Hom_M(M * F_2, M)` with type (A)
(`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`, Theorem E,
`n = 2`). BFFHZ l.349--350: "we analyze the (right) action of Aut_G(G ∗ F_n) on
Hom_G(G ∗ F_n; G) by precomposition", and l.640--647 prove that this action is of
type (A).
- Use the left action `α·φ = φ ∘ α^(-1)`. It has the same orbits and the same
  stabilizers, so it is again of type (A).
- BFFHZ l.114--116: "elements of Hom_G(G∗F_n; G) are in one-to-one correspondence
  with ordered n-tuples of elements of G". Identify `S = M × M` through
  `φ -> (φ(x_1), φ(x_2))`.

**3. The embedding.** BFFHZ l.661--663: "G embeds in Aut_G(G ∗ F_2), for example by
sending g to the G-automorphism that takes x_1 to x_1 g and fixes x_2".
- Write `τ_g` for this automorphism.
- Since `τ_g` fixes `M` pointwise, `τ_g τ_h (x_1) = τ_g(x_1 h) = x_1 g h`. So
  `g -> τ_g` is a homomorphism, and it is injective because `τ_g(x_1) = x_1 g`.
  This is the check already written in `pbh-relative-free-group-automorphisms-proof`.

**4. Freeness.** For `φ ∈ S` and `g ∈ M`:

```text
(τ_g · φ)(x_1) = φ(τ_(g^-1)(x_1)) = φ(x_1 g^-1) = φ(x_1) g^-1,    (τ_g · φ)(x_2) = φ(x_2),
```

because `φ` restricts to the identity on `M`. So `τ_g` acts on `M × M` by
`(m_1, m_2) -> (m_1 g^(-1), m_2)`, and fixes a point only if `g = 1`. So every point
of `S` has trivial stabilizer in `τ(M)`, hence in `τ(G)`.

**5. Infinitely many orbits.** The second coordinate `m_2` is invariant under
`τ(M)`, so there are at least `|M|` orbits. `M` is infinite. A MIF group satisfies no
nontrivial mixed identity. If `|M| = k` were finite, the nontrivial word `x^k` in
`M * ⟨x⟩` would be sent to `1` by every `M`-homomorphism to `M`. BFFHZ l.360--362:
"Recall that a group G is called mixed identity-free (MIF) if for all n and all
1 ≠ w ∈ G∗F_n, there exists a G-homomorphism φ: G∗F_n → G such that φ(w) ≠ 1."

**6. Free `G`-sets.** A countable free `G`-set is a disjoint union of at most
countably many copies of `G`. Send the copy indexed by `i` to the orbit of a
representative `s_i ∈ S`, with distinct orbits for distinct `i`, by `g -> τ_g · s_i`.
- The map is `G`-equivariant.
- It is injective on each copy by step 4.
- It is injective across copies because the orbits are distinct.

This is possible since there are infinitely many orbits and `S` is countable. `∎`
