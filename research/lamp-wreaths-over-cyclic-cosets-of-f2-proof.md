---
rg: 2
id: lamp-wreaths-over-cyclic-cosets-of-f2-proof
kind: route
title: Build a ping-pong copy of F_2 in Thompson's V in which <a> is the exact stabilizer of a clopen set, then apply the clopen-orbit wreath lemma
target: lamp-wreaths-over-cyclic-cosets-of-f2-lie-in-b-a
requires:
  - wreaths-over-clopen-stabilizer-cosets-lie-in-b-a
  - thompson-v-finitely-presented-infinite-simple
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed.

**0. The host.**
- Let `Y = {0,1}^N`, with `[w]` the cone of words beginning with `w`, and let `V` be
  Thompson's group of finite prefix-replacement homeomorphisms of `Y`.
- `V` is finitely presented (`thompson-v-finitely-presented-infinite-simple`).
- *Full.* A `V`-local homeomorphism agrees with prefix replacements on the cones of a finite
  partition. The restriction of a prefix replacement `u·x ↦ v·x` to a subcone `[uw]` is the
  prefix replacement `uw·x ↦ vw·x`. So a `V`-local homeomorphism lies in `V`.
- *Clopen transitive:* recorded in `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.
- *Consequence.* Full plus clopen transitive give an element of `V` mapping `A` onto `A'`
  whenever `A, A'` are proper nonempty clopen sets: glue a local map `A -> A'` with a local
  map `Y∖A -> Y∖A'`.

**1. The generator `α`.** Let `t ∈ V` be Thompson's `x_0`:
`0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w`.
- One checks `t^n([10]) = [0^n 1]` for `n ≥ 1` and `t^(-n)([10]) = [1^(n+1) 0]` for `n ≥ 1`.
- So the translates `t^n([10])`, `n ∈ Z`, are pairwise disjoint.
- Let `U = [0]` and `W = [1]`. Define `α` as the identity on `U` and `1w ↦ 1·t(w)` on `W`.
  Then `α ∈ V`, `α(U) = U`, and `α` has infinite order.
- With `Q = [110] ⊂ W`: `α^n(Q) = 1·t^n([10]) ⊆ W ∖ Q` for every `n ≠ 0`.

**2. The generator `β`.** Let `Q_+ = [1100]` and `Q_- = [1101]`, so `Q = Q_+ ⊔ Q_-`. By step 0,
choose `β ∈ V` with `β(Y ∖ Q_-) = [11000]` and hence `β(Q_-) = Y ∖ [11000]`.
- *Forward.* `β(Y ∖ Q_-) ⊆ Q_+ ⊆ Y ∖ Q_-`, so `β^m(Y ∖ Q_-) ⊆ Q_+` for all `m ≥ 1`.
- *Backward.* `β^(-1)(Y ∖ Q_+) ⊆ β^(-1)(Y ∖ [11000]) = Q_- ⊆ Y ∖ Q_+`, so
  `β^(-m)(Y ∖ Q_+) ⊆ Q_-` for all `m ≥ 1`.
- *Ping-pong.* With `P = Y ∖ Q`: `β^m(P) ⊆ Q` for all `m ≠ 0`, and `U ⊆ P` (as `U ∩ W = ∅`).

**3. The key computation.** Let `w = α^(n_0) β^(m_1) α^(n_1) ⋯ β^(m_k) α^(n_k)` with `k ≥ 1`, all
`m_i ≠ 0` and `n_1, …, n_(k-1) ≠ 0`.
- Then `α^(n_k)(U) = U ⊆ P` and `β^(m_k)(U) ⊆ Q`.
- Inductively, `α^(n_i)(Q) ⊆ P` for `n_i ≠ 0` and `β^(m_i)(P) ⊆ Q`. So
  `β^(m_1) α^(n_1) ⋯ α^(n_k)(U) ⊆ Q`, and `w(U) ⊆ α^(n_0)(Q)`.
- Since `α` preserves `U` and `Q ∩ U = ∅`, `α^(n_0)(Q) ∩ U = α^(n_0)(Q ∩ U) = ∅`. So
  `w(U) ∩ U = ∅`, and `w(U) ≠ U`.

**4. Consequences.**
- *Freeness.* Every reduced word in `α, β` containing `β` moves `U`, so it is not the
  identity. The nonzero powers of `α` are nontrivial because `α` has infinite order. So
  `a ↦ α`, `b ↦ β` gives an isomorphism `F_2 ≅ G := ⟨α, β⟩ ≤ V`.
- *Exact stabilizer.* By step 3, `Stab_G(U) = ⟨α⟩`.

**5. Conclusion.** Apply `wreaths-over-clopen-stabilizer-cosets-lie-in-b-a` with `D = V`, `G`,
`U` and `H = K = ⟨α⟩`. The isomorphism `F_2 ≅ G` carries `⟨a⟩` to `⟨α⟩`, so
`L ≀_{F_2/⟨a⟩} F_2 ≅ L ≀_{G/⟨α⟩} G ∈ B_A`. ∎
