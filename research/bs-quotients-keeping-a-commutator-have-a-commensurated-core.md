---
rg: 2
id: bs-quotients-keeping-a-commutator-have-a-commensurated-core
kind: claim
title: In every quotient of BS(m,n) (gcd(m,n) = 1, |m|, |n| ≥ 2) that keeps [tat^-1, a] nontrivial, the kernel is free, the image of <a> is an infinite cyclic commensurated core-free subgroup whose normal closure is the kernel of a modular character onto Z, and an isolated such quotient has a rigid normal structure
requires:
  - coprime-baumslag-solitar-images-in-va-are-metabelian
  - fp-groups-with-a-locally-moving-simple-subgroup-are-isolated
distinct_from:
  coprime-baumslag-solitar-images-in-va-are-metabelian: that shows one host class (VA) kills the commutator; this describes every quotient that keeps it, with no host assumed.
  bs-quotients-keeping-a-commutator-need-distortion: that turns item 2 of this node into exclusions of host classes by distortion; this is the structure theorem itself.
  every-decidable-group-is-a-limit-of-isolated-groups: that is Cornulier--Guyot--Pitsch Question 1; this constrains every isolated group near its test case BS(2,3).
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed).

**Setting.** `G = BS(m,n) = ⟨a, t | t a^m t^{-1} = a^n⟩` with `gcd(m,n) = 1` and `|m|, |n| ≥ 2`,
acting on its Bass--Serre tree `T` (vertex set `G/⟨a⟩`). `K = ker(G → Z, t ↦ 1, a ↦ 0) = ⟨⟨a⟩⟩`.
`c = [t a t^{-1}, a]`, nontrivial in `G` by Britton's lemma. Let `N ⊴ G` with `c ∉ N`,
`Q = G/N`, `α = aN`, `τ = tN`, `A = ⟨α⟩`, `K_Q = KN/N = ⟨⟨α⟩⟩_Q`.

**Statement.**
1. **Free kernel.** `N ∩ g⟨a⟩g^{-1} = 1` for every `g`. So `N` acts freely on `T` and is a free
   group, `α` has infinite order, and `Q` acts faithfully on the graph `X = N\T`, transitively on
   vertices, with vertex stabilizers the conjugates of `A ≅ Z`.
2. **Commensurated core.** `A` is commensurated in `Q` and core-free. For `g ∈ Q` choose `j ≠ 0`
   with `g α^j g^{-1} = α^k`; then `Δ(g) = k/j` is a well-defined homomorphism `Δ: Q → Q^×` with
   `Δ(α) = 1`, `Δ(τ) = n/m`. Its kernel is `K_Q`, and `Q/K_Q ≅ Z`. Every element of `K_Q`
   centralizes a nonzero power of `α`. Every `A`-orbit on `Q/A` is finite, of size dividing a power
   of `mn`.
3. **Normal subgroups meeting `A`.** If `L ⊴ Q` meets some conjugate of `A` nontrivially, then
   `L ⊇ K_Q' ∋ c`, and `Q/L` is a quotient of `Z/d ⋊ Z` for some `d` prime to `mn`.
4. **Isolated quotients.** Suppose `Q` is finitely discriminable. Then:
   - (a) every minimal normal subgroup of `Q` lies in `K_Q`;
   - (b) a minimal normal subgroup that meets a conjugate of `A` nontrivially equals `K_Q'`, so there
     is at most one, and then `Q/K_Q' ≅ Z/d ⋊ Z` with `gcd(d, mn) = 1`;
   - (c) if moreover some element of `K'' − {1}` survives in `Q`, that subgroup `K_Q'` is perfect;
   - (d) if `K_Q'` is minimal, every other minimal normal subgroup is cyclic of prime order dividing `d`.
5. **Finitary monoliths.** Suppose `Q` acts faithfully on a set `S`, `|S| ≥ 5`, with
   `Alt_fin(S) ≤ Q`. Then:
   - (a) `α` acts on `S` with all orbits finite and of unbounded size, and no nonzero power of `α` is
     finitary;
   - (b) `P' = Q/(Q ∩ FSym(S))` is a quotient of `G` in which `a` has infinite order;
   - (c) the kernel `N'` of `G → P'` is free and nontrivial, so `P'` is a proper quotient of `G`;
   - (d) `P'` is finitely presented if `Q` is.

   So an isolated group of this kind near `G` needs a finitely presented proper quotient `P'` of `G`
   in which `a` has infinite order, almost-acting on `S` with finite `a`-orbits. The base need not
   keep `c`. For `BS(2,3)` the canonical candidate is `P' ≅ G` through the non-Hopfian surjection
   `a ↦ a^2, t ↦ t`, whose kernel is `⟨⟨c⟩⟩` (Remark 2).

**Proof.**
1. Suppose `g a^k g^{-1} ∈ N` with `k ≠ 0`. Then `a^k ∈ N`, so `α` has finite order. By item 2 of
   `coprime-baumslag-solitar-images-in-va-are-metabelian` (valid in any group), `⟨α⟩` is normal and
   `τατ^{-1} ∈ ⟨α⟩` commutes with `α`, so `c ∈ N`. This is a contradiction. Vertex stabilizers of `T`
   are the `g⟨a⟩g^{-1}` and `G` acts without inversions, so `N` acts freely and is free. The
   stabilizer in `Q` of the vertex `N·g⟨a⟩` of `X` is `N g⟨a⟩g^{-1}/N`, a conjugate of `A`. The
   kernel of `Q ↷ X` is a normal subgroup inside `A`; it is trivial by item 2 (core-free).
2. `⟨a⟩` is commensurated in `G`: for each `g`, `⟨a⟩ ∩ g⟨a⟩g^{-1}` is the pointwise stabilizer of
   the geodesic from `v = ⟨a⟩` to `gv`, of index in `⟨a⟩` dividing `(mn)^{d(v,gv)}` (each edge has
   index `|m|` or `|n|` in its endpoint stabilizers). Images of finite-index subgroups have finite
   index, so `A` is commensurated in `Q`, and the index `[A : A ∩ gAg^{-1}]`, which is the size of
   the `A`-orbit of `gA`, divides a power of `mn`.
   - *Core-free.* If `⟨α^k⟩` is normal (`k ≠ 0`), then `τ α^k τ^{-1} = α^{εk}` with `ε = ±1`. Then
     `α^{nk} = τ α^{mk} τ^{-1} = α^{εmk}`, and `α` has finite order because `n ≠ εm`. This
     contradicts item 1.
   - *`Δ` is well defined.* If `gα^jg^{-1} = α^k` and `gα^{j'}g^{-1} = α^{k'}`, then
     `gα^{jj'}g^{-1}` equals both `α^{kj'}` and `α^{jk'}`, so `kj' = jk'`, since `α` has infinite
     order. It is a homomorphism, by composing the relations for suitable common multiples of the
     exponents.
   - *Kernel of `Δ`.* `Δ(α) = 1`, so `Δ` kills `K_Q`. `Q/K_Q` is generated by `τ`, and `Δ(τ) = n/m`
     has infinite order. So `Q/K_Q ≅ Z` and `ker Δ = K_Q`.
   - *Centralizers.* Each conjugate `gαg^{-1}` commutes with `g α^{j'} g^{-1} = α^{k}`, where
     `⟨α^k⟩ = A ∩ gAg^{-1}`. A finite product of elements, each commuting with some `α^{k_i}`,
     commutes with `α^{lcm k_i}`.
3. Let `gα^kg^{-1} ∈ L`, `k ≠ 0`. Then `α^k ∈ L`. In `Q/⟨⟨α^k⟩⟩` the image `ᾱ` has finite order, so
   by the same finite-order lemma its order `d` is prime to `mn`, `⟨ᾱ⟩` is normal, and
   `Q/⟨⟨α^k⟩⟩ = ⟨ᾱ⟩⟨τ̄⟩`. Hence `K_Q/⟨⟨α^k⟩⟩ = ⟨ᾱ⟩` is abelian, so
   `K_Q' ≤ ⟨⟨α^k⟩⟩ ≤ L`. Finally `c = [τατ^{-1}, α] ∈ K_Q'`.
4. For (a): let `M` be minimal normal. `M ∩ K_Q` is `1` or `M`. If it is `1`, then `M` embeds in
   `Q/K_Q ≅ Z`, so `M ≅ Z`. But then `M^2` is a characteristic, nontrivial, proper subgroup, hence
   normal in `Q`, which contradicts minimality.

   For (b): by item 3, such an `M` contains `K_Q' ≠ 1`, and minimality gives `M = K_Q'`. With `k` as
   in item 3, `M ≤ ⟨⟨α^k⟩⟩ ≤ M`, so `Q/M = ⟨ᾱ⟩⋊⟨τ̄⟩`. Here `τ̄` has infinite order, because
   `Δ(τ^j) ≠ 1` for `j ≠ 0` and `Δ` factors through `Q/M` (`M ≤ K_Q`).

   For (c): `K_Q'' ≠ 1` is characteristic in `M = K_Q'`, hence normal in `Q`, so `K_Q'' = M`.

   For (d): another minimal normal `M_1` meets `M` trivially and lies in `K_Q` by (a), so it embeds
   in `K_Q/M ≅ Z/d`. A minimal normal cyclic group has prime order.
5. For (a): `Alt_fin(S)` is the unique minimal normal subgroup of `Q` by
   `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated` (case (fin), item 3), so it lies in
   `K_Q` by 4(a). So every 3-cycle `σ = (x y z)` commutes with some `α^j`, `j ≠ 0`. Then `α^j`
   permutes `{x, y, z}`, so `α^{6j}` fixes `x`: every orbit is finite. A nonzero finitary power
   `α^k` would have finite order. Then `α` would have finite order, against item 1. Bounded orbit
   sizes would likewise give `α^{lcm} = 1`.

   For (b): if `a^k ↦ 1` in `P'` with `k ≠ 0`, then `α^k ∈ FSym(S)` has finite order, the same
   contradiction.

   For (c): `N' ∩ ⟨a⟩ = 1` by (b). As in item 1, `N'` acts freely on `T` and is free. If `N'` were
   trivial, `G → Q` would be injective. Then `Q ≅ G` would be torsion-free, but it contains
   `Alt_fin(S)`.

   For (d): `Q ∩ FSym(S)` is `Alt_fin(S)` or `FSym(S)`, the normal closure in `Q` of one 3-cycle,
   together with one transposition in the second case. So `P'` is a quotient of `Q` by a finitely
   normally generated subgroup.

**Remark 1 (hosts that satisfy every condition).** Let `T` be the Bass--Serre tree of `BS(2,3)` and
`RP` the rigid permutation group of `V(T)` in the sense of Bux--Llosa Isenrich--Wu
(`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`). Every piece of a rigid permutation
is a half-tree, and the pointwise stabilizer of a half-tree in `BS(2,3)` is trivial: an element
`a_w^k` fixing four edges at `w` has `6 | k`, and going up multiplies the exponent by `2/3`. So each
piece has a well-defined `t`-exponent. Let `RP^Δ` be the subgroup of rigid permutations all of whose
pieces have the same `t`-exponent.
- `RP^Δ` contains `BS(2,3)` and `FSym(V(T))`.
- `⟨a⟩` is commensurated in `RP^Δ`, and the common exponent is a homomorphism `RP^Δ → Z`.
- Every element of its kernel centralizes a power of `a`, since `a` has finite orbits on `V(T)`.
- `Alt_fin(V(T))` is the monolith.

So `RP^Δ` has exactly the shape items 2, 4 and 5 force, with `α = a`, `τ = t`. Whether `RP^Δ` is
finitely presented, and whether a finite-index subgroup of it is generated by a pair satisfying the
`BS(2,3)` relation with no short extra relations, is open.

**Remark 2 (the non-Hopfian kernel).** For `BS(2,3)` the classical surjection `φ: G → G`, `a ↦ a^2`,
`t ↦ t`, has kernel exactly `⟨⟨c⟩⟩`. In `G/⟨⟨c⟩⟩` put `β = tat^{-1}` and `x = βa^{-1}`. Since `β` commutes with
`a` and `β^2 = a^3`, we get `x^2 = a`, `x^3 = β` and `t x^2 t^{-1} = x^3`, so `x ↦ x, s ↦ t` defines
`G → G/⟨⟨c⟩⟩` (`G = ⟨x, s | s x^2 s^{-1} = x^3⟩`). It is inverse to `G/⟨⟨c⟩⟩ → G`, `a ↦ x^2`, `t ↦ s`,
which is well defined because `s x^4 s^{-1} = x^6` and `[s x^2 s^{-1}, x^2] = [x^3, x^2] = 1`. The composite
`G → G/⟨⟨c⟩⟩ ≅ G` is `φ`.
