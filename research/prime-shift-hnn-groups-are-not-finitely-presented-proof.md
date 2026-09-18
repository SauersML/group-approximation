---
rg: 2
id: prime-shift-hnn-groups-are-not-finitely-presented-proof
kind: route
title: Kill the unipotent normal closure to reach Z/2 x (Z wr Z), and use the Bass--Serre tree for finitary elements
target: prime-shift-hnn-groups-are-not-finitely-presented
requires:
  - gl-n-q-lies-in-prime-shift-permutation-group
---

Write `Π = A *_C B` with `A = GL_n(Q)`, `C = N_n(Q)` and `B = C ⋊_α <s>`; for
`n = 1`, `A = Aff(Q)` and `C = Q^x`.

**The quotient.**
- Let `M ⊴ A` be the normal closure of `x_12(1)`, respectively of `τ`.
  - For `n >= 2`, `M = SL_n(Q)`: diagonal conjugation gives every `x_12(r)`,
    `r != 0`; signed permutations give every `x_ij(r)`; and these generate
    `SL_n(Q)`.
  - For `n = 1`, `M = Q`, the translations: `m_a τ m_a^-1 = (x -> x+a)`.
- By the universal property of amalgams, a homomorphism from `Π / <<M>>` is a pair
  of homomorphisms on `A` and `B` that agree on `C` and kill `M`. So
  `Π / <<M>> = B / <<C ∩ M>>_B`, and `C ∩ M` is normal in `B`:
  - for `n = 1`, `C ∩ M = 1` and `C -> A/M` is an isomorphism;
  - for `n >= 2`, `C ∩ M = ker(det|_C)`, and `det(α(c)) = σ(det c)`, so `α`
    preserves it.
- `det: C -> Q^x` is onto and intertwines `α` with `σ`. So
  `Π / <<M>> ≅ Q^x ⋊_σ <s>`.
- `Q^x = {±1} × ⊕_(k in Z) p_k^Z`, with `σ` fixing `-1` and shifting `k`. So
  `Q^x ⋊_σ <s> ≅ Z/2 × (Z ≀ Z)`.

**Item 1.**
- `Z ≀ Z` is not finitely presented: Baumslag, Math. Z. 75 (1961), a restricted
  wreath product `A ≀ B` is finitely presented only if `A` is trivial or `B` is
  finite.
- It is a retract of `Z/2 × (Z ≀ Z)`, so that group is not finitely presented
  either.
- A quotient of a finitely presented group by the normal closure of finitely many
  elements is finitely presented. So `Π` is not.
- `Π` is finitely generated, by `GL_n(Z)`, `e` and `s`
  (`gl-n-q-lies-in-prime-shift-permutation-group`).

**Item 2.**
- Suppose `A_1` is finitely presented. Then `Q_1 = A_1 / <<τ>>_(A_1)` is finitely
  presented, and it is a quotient of `W = Z/2 × (Z ≀ Z)`.
- Let `K` be the kernel of `W -> Q_1`. `K != 1`, since `W` is not finitely
  presented. Let `L = ⊕_Z Z` be the base of `Z ≀ Z`.
- **`K` meets `Z ≀ Z`.** Suppose `K ∩ (Z ≀ Z) = 1`. Every element of `K` squares
  into `K ∩ (Z ≀ Z)`, and `Z ≀ Z` is torsion-free, so `K` is the `Z/2` factor.
  Then `Q_1 = Z ≀ Z` is not finitely presented, a contradiction.
- **`K` meets `L`.** Put `K' = K ∩ (Z ≀ Z) != 1`, which is normal in `Z ≀ Z`.
  If `K' ∩ L = 0`, then `[K', L] ⊆ K' ∩ L = 0`, so `K'` centralizes `L`. The
  centralizer of `L` in `Z ≀ Z` is `L`, so `K' ⊆ L`, contradicting `K' != 1`.
- `L` is the group of positive dilations `m_r`, `r in Q_>0`. So some `m_r` with
  `r != 1` maps to `1` in `Q_1`, that is, `m_r ∈ <<τ>>_(A_1)`.
- For `K_n` the same argument applies with `diag(r,1,...,1)` and `x_12(1)`.
- In `Π` itself, `m_r` is not in `<<M>>`, since it survives in `Π / <<M>>`. So
  the surjection is not injective.

**Item 3.** Assume `Π_1 -> A_1` is injective, and let `N = A_1 ∩ FSym(Q)`.
- `N` is normal and locally finite.
- **`N` fixes a vertex.** `N` acts on the Bass--Serre tree `T` of
  `Π_1 = A *_C B`. Every finitely generated subgroup of `N` is finite, so it
  fixes a vertex. So either `N` fixes a vertex, or it fixes a unique end.
  - A fixed end of `N` would be fixed by `Π_1`.
  - A group fixing an end has a Busemann homomorphism to `Z` that vanishes on
    elliptic elements. `A` and `B` are vertex stabilizers and generate `Π_1`, so
    every element of `Π_1` would be elliptic.
  - But `a b` is hyperbolic for `a ∈ A \ C` and `b ∈ B \ C`. So `N` fixes a
    vertex.
- **`N` fixes `T`.** `Fix(N)` is a nonempty `Π_1`-invariant subtree, since `N`
  is normal. The tree of a proper amalgam is minimal (`C != A, B`), so `N` fixes
  all of `T`.
- **`N = 1`.** Then `N ⊆ C = Q^x`, and the torsion of `Q^x` is `{±1}`. But
  `x -> -x` has infinite support, so `N = 1`.
- **Converse direction.** `A_1` is 2-transitive, hence primitive. By the
  Jordan--Wielandt theorem, a primitive group containing a nontrivial finitary
  permutation contains `Alt_fin`.

**Item 4.**
- **`n = 1`.** `Aff(Q)^ab = Q^x`: the translations are commutators
  `[m_a, τ_b] = τ_((a-1)b)`. Since `C = Q^x` maps isomorphically onto `A^ab`, the
  pushout of abelianizations is `B^ab`. That is `(Q^x)_σ × <s>`, and
  `(Q^x)_σ = Z/2 × Z`.
- **`n >= 2`.**
  - `SL_n(Q)` is perfect, so `A^ab = Q^x` via `det`.
  - `C^ab = Q^x × Z/2`, via the product of the diagonal entries and the sign of
    the permutation.
  - The pushout identifies `C^ab` with `A^ab` through `det` and kills
    `ker(det) = <(-1, -1)> ≅ Z/2`.
  - This leaves `((Q^x)_σ × Z/2) / Z/2 × <s> ≅ Z/2 × Z × Z`.
