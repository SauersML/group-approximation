---
rg: 2
id: hnn-stages-add-no-complexity-beyond-edge-distortion
kind: claim
title: A faithful one-permutation HNN stage over a type (A) actor adds no complexity beyond the distortion of its orbit-finite edge groups, and an identity edge must be closed under the permutation bicommutant, which fiber-product edges never are
distinct_from:
  stable-permutation-hnn-of-type-a-actor-is-type-a: that proves the stage is of type (A) when rho is injective; this bounds the orbit problem of the stage and gives necessary conditions for injectivity.
  permutation-hnn-realization-of-type-a-actor-is-a2: that treats the non-injective case and asks when the kernel is recursive; this is the injective case, measured in complexity.
  explicit-type-a-actor-with-non-pr-orbit-problem: that is the open premise of the Kourovka 7.19 route; this shows that one-permutation HNN stages over a primitive recursive base can meet it only through edge groups whose distortion is not primitive recursive.
  type-a-actors-with-arbitrarily-hard-word-problem: that is the complexity root for actors; this is a conservation law that tells a construction by HNN stages where its hardness has to come from.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed). Item 5(c) uses a
recalled fact about pushdown systems and is marked there.

## Setting

We use the setting of `stable-permutation-hnn-of-type-a-actor-is-type-a`:
- `Γ ↷ X` is of type (A);
- `D_1, D_2 ≤ Γ` are finitely generated, `ψ : D_1 → D_2` is an isomorphism, and `π ∈ Sym(X)` satisfies
  `π d π^-1 = ψ(d)` for `d ∈ D_1`;
- `L = Γ*_ψ`, and `ρ : L → Sym(X)` extends the action by `t ↦ π`.

**Assume `ρ` is injective, and that `D_1` and `D_2` have finitely many orbits on `X`.**

Encode a point of `X` as a word `g` over the generators of `Γ` together with an index `i`, standing for
`g·z_i`, where the `z_i` are fixed representatives of the `Γ`-orbits. Then `OP(Γ,X)`, as in
`twisted-brin-thompson-wp-equals-actor-orbit-problem`, decides equality of encoded points. For `D = D_k`,
fix representatives `x_1, …, x_r` of its orbits and a finite generating set. Define:
- the **orbit distortion** `Δ_D(n)`: the maximum, over encoded points `p` of length `≤ n`, of the least
  `|δ|` with `δ` a word in `D` and `p = δ x_j` for some `j`;
- the **subgroup distortion** `Σ_D(n)`: the maximum of `|γ|_D` over `γ ∈ D` with `|γ|_Γ ≤ n`;
- `MEM(D)`: membership of words over `Γ` in `D`.

## Statement

1. **Rigidity.** `π(δ x_j) = ψ(δ) π(x_j)` for all `δ ∈ D_1`. So `π` is determined by the `r` points
   `π(x_j)`, and the realizing permutations form one coset `π · C_{Sym X}(D_1)`.
2. **Complexity budget.** `OP(L,X)` is primitive recursive relative to `OP(Γ,X)` and the functions
   `Δ_{D_k}`, `Σ_{D_k}`, `MEM(D_k)` for `k = 1, 2`. If all of these are primitive recursive, so is
   `OP(L,X)`, and by (c) of `twisted-brin-thompson-wp-equals-actor-orbit-problem` so is the word problem
   of the finitely presented simple group `SV_L`.
3. **Transporter condition.** `D_1 = {γ ∈ Γ : π γ π^-1 ∈ Γ}`.
4. **Bicommutant condition for identity edges.** Suppose `D_1 = D_2 = D` and `ψ = id`. Write `D'` for the
   centralizer of `D` in `Sym(X)` and `D''` for the centralizer of `D'`. Then `D = C_Γ(π) = Γ ∩ D''`.
5. **Consequences.**
   - (a) *Regular edges pass (4).* If `D` acts freely on `X` with finitely many orbits, then `D'' = D`.
   - (b) *Fiber-product edges fail (4).* Let `Γ = Γ_1 × Γ_2` act on `X_1 ⊔ X_2` factorwise. Take
     `P ≤ Γ_1`, `P' ≤ Γ_2`, and surjections `p : P → Q`, `p' : P' → Q` onto a nontrivial group, with
     kernels `N`, `N'`. Suppose `N` acts nontrivially on every `P`-orbit in `X_1`, and `N'` on every
     `P'`-orbit in `X_2`. Then every permutation commuting with `D = {(u,v) : p(u) = p'(v)}` commutes
     with `P × P' ⊋ D`. So no identity-edge stage over such a `D` is injective. This covers
     Mihailova-type edges that are orbit-finite, such as `Γ(2) ×_Q Γ(2)` in `T × T`, acting on two copies of the dyadic
     points of the circle (`P^1(Q)` in the Farey model, where `Γ(2) ≤ PSL_2(Z) ≤ T` has three cusp orbits). Their membership problem is as hard as the word problem of `Q`.
   - (c) *Over Thompson's `V`, orbit distortion is tame.* Let `V` act on a tail class of `{0,1}^N`, and
     let `D ≤ V` be finitely generated. Then `D` acts by the invertible rules of a pushdown system (prefix
     replacement, with the tail as bottom symbol). Its orbits are reachability classes, and `Δ_D` is
     primitive recursive. *Recalled, not re-read:* the set of configurations reachable from a regular set
     is regular and effectively computable (Büchi 1964; Bouajjani–Esparza–Maler 1997), and shortest
     runs between two configurations are at most exponentially long in their sizes. So a `V`-based
     stage can gain complexity only through `Σ_D` or `MEM(D)`.

## Proof

1. Apply `π d π^-1 = ψ(d)` to `x_j`. Two realizations differ by a permutation commuting with `D_1`.
2. **The word problem of `L`.** Use Britton reduction. A pinch `t γ t^-1` with `γ ∈ D_1` is decided by
   `MEM(D_1)`. Rewrite `γ` as a `D_1`-word of length `≤ Σ_{D_1}(|γ|)`, found by bounded search checked with
   `OP(Γ,X)`, and substitute `ψ(γ)`. Pinches `t^-1 γ t` are handled with `D_2`. A word of length `ℓ` has at
   most `ℓ` pinches, and each multiplies lengths by at most a primitive recursive function of `Σ`. At the
   end, `OP(Γ,X)` decides the remaining `Γ`-word.

   **Stabilizer membership.** Apply the letters of `ℓ` to an encoded point, right to left.
   - A `Γ`-letter is prepended to the encoding.
   - For `π^{±1}`, search `D_{1/2}`-words up to length `Δ(|p|)` for `δ` and `j` with `p = δ x_j`,
     testing equality with `OP(Γ,X)`, and output `ψ^{±1}(δ)·π^{±1}(x_j)`, whose encodings are fixed.

   Lengths after `m ≤ ℓ` letters are bounded by an `m`-fold iterate of a primitive recursive function of
   `Δ` and `Σ`, and the final comparison is `OP(Γ,X)`. Bounded iteration and composition preserve
   primitive recursiveness relative to the oracles.
3. If `π γ π^-1 = γ' ∈ Γ`, then `ρ(t γ t^-1 γ'^-1) = 1`. By injectivity `t γ t^-1 = γ'` in `L`, and by
   Britton's lemma `γ ∈ D_1`. The reverse inclusion holds by definition.
4. By 3 with `ψ = id`, `C_Γ(π) = D`. Since `π ∈ D'`, every element of `D''` commutes with `π`, so
   `Γ ∩ D'' ⊆ C_Γ(π) = D ⊆ Γ ∩ D''`.
5. (a) `D' ≅ D^r ⋊ Sym(r)`: right multiplications on each orbit, and swaps of the identified orbits. An
   element of `D''` preserves the support of each nontrivial right multiplication, hence each orbit. On
   an orbit it commutes with all right multiplications, so it is a left multiplication by some `d_j`.
   Commuting with the swaps gives `d_1 = ⋯ = d_r`.

   (b) Let `σ` commute with `D`. Then `D_{σx} = D_x`. For `x ∈ X_1`, `D_x ⊇ 1 × N'`, a normal subgroup of
   `D`. If `σx ∈ X_2`, then `N'` fixes the whole orbit `D·σx = P'·σx`, which is excluded. So `σ` preserves
   `X_1` and `X_2`. On `X_1` the group `D` acts through `pr_1(D) = P`, and on `X_2` through `P'`, so `σ`
   commutes with `P × P'`. Finally `D ≠ P × P'` because `Q ≠ 1`.

   (c) The generators act by finitely many prefix replacements, which are pushdown rules once the
   tail is read as the bottom symbol; apply the recalled facts. ∎

## Without injectivity

Item 1 and the stabilizer-membership half of item 2 never use injectivity of `ρ`. Evaluating the image
group `⟨Γ, π⟩` on encoded points is primitive recursive relative to `OP(Γ,X)` and `Δ_{D_1}`, `Δ_{D_2}`,
whether or not `ρ` is injective. The only further source of complexity is the word problem of
`⟨Γ, π⟩` itself. By (a) of `permutation-hnn-realization-of-type-a-actor-is-a2`, that word problem is
the recursion problem of the free kernel `K = ker ρ`. So complexity enters a one-permutation stage in
exactly two ways:
- the distortion of an edge group, in the injective case;
- the kernel, in the non-injective case.

The kernel case pays for this with finite presentation of the image `L/K`, which is not automatic
(`a2-action-with-non-finitely-presented-image`).

The other constructions of type (A) actors on main are conservative for a simpler reason: their actions
are computed coordinatewise from the inputs' actions. These are products and finite wreaths
(`type-a-actions-closed-under-products-and-finite-wreaths`), type (A) lamp wreaths
(`type-a-actors-closed-under-type-a-lamp-wreaths`), and towers of twisted Brin--Thompson groups (the
iteration clause of `twisted-brin-thompson-wp-equals-actor-orbit-problem`). The one-permutation stage was
the only construction on this list whose new generator is an arbitrary permutation. This node shows that
even that generator is pinned by finitely many values.

## What survives for hard actors

Items 2–5 place the complexity of any tower of injective one-permutation stages in the distortion of its
edges. Take a base whose orbit problem `OP(Γ,X)` is primitive recursive, such as `V`, `T` or `F`, and
ask for a stage whose orbit problem is not primitive recursive, as `explicit-type-a-actor-with-non-pr-orbit-problem` needs. Then some
orbit-finite edge must have non-primitive-recursive `Δ`, `Σ` or `MEM`. For identity edges it must also be
bicommutant-closed, which rules out the fiber-product source of hard membership. The cleanest surviving
shape is a **regular** orbit-finite edge `D`. With one orbit this is an exact factorization
`Γ = D · Γ_x`, `D ∩ Γ_x = 1`, and `Δ_D` is the length blow-up of the factorization `g = δ p`. So the
remaining question is whether a finitely presented type (A) actor admits an exact factorization with
non-primitive-recursive factorization distortion. The distortion of that single subgroup is the whole
budget.

## Lesson for general BH

Complexity is conserved along HNN stages. The stable letter is pinned by finitely many values, so the
new orbit problem is the old one plus the distortion of the edge groups. Finite presentation and type (A)
come for free in these stages, but hardness does not. Hard type (A) actors, needed for the complexity
root, for Kourovka 7.19, and hence for Boone--Higman itself, cannot be built by stacking such stages over
a tame base unless some orbit-finite edge is already badly distorted. Identity edges must be
bicommutant-closed, which excludes the Mihailova route to hard membership. The one remaining shape is a
regular orbit-finite edge, and there hardness means factorization distortion.
