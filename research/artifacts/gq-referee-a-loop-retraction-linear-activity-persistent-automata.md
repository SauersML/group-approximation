# Referee report (gq-referee-a, proof-gap lens): loop retraction, linear-activity automata, persistent subexponential automata

**Reviewed** (lane bh-self-similar, 70ac9f576), read on origin/main:
- `loop-retraction-forces-fp-eventual-section-groups` and its `-proof`;
- `linear-activity-automata-can-have-non-fp-nekrashevych-groups`, with the proof inline;
- `persistent-subexponential-automata-generate-finite-groups`, with the proof inline.

**Verdict: PASS for all three.**
- There is one nit.
- The only unrefereed input is the necessity half of Theorem A of `rover-nekrashevych-fp-iff-finite-lift-presentation`,
  as the nodes say. It is not rechecked here.
- The non-finite-presentation of the Grigorchuk group is a cited node.

## 1. Loop retraction
- **The section endomorphism.**
  - All letters fix `x`, so `w|_x = ∏ s_k|_x` by the cocycle rule, and `σ` extends to an endomorphism of `F`.
  - `σ^p` is idempotent on `S`, so it is the identity on `S_∞`. Also `σ(S_∞) = σ^p(σ(S)) ⊆ S_∞`, so `θ = σ|_(S_∞)` is a
    permutation of order `q`.
  - `π = σ^p` retracts `F` onto `F_∞`, and `σ∘π = σ^(p+1) = θ∘π`.
  - `N` is section-closed, so `σ(N) ⊆ N`. ✓
- **`M'`.** `θ` permutes the generating set `{θ^jπ(r)}`, so `M'` is `θ`-invariant with `θ^(−1)(M') = M'`. Also
  `θ^jπ(r) = r|_(x^(p+j)) ∈ N ∩ F_∞`. ✓
- **The key step (the author asked about this).** For `w ∈ L(M_α)`, the section `σ(w) = w|_x` lies in `M_α`.
  - So `θ(π(w)) = π(σ(w)) ∈ π(M_α) ⊆ M'`, and hence `π(w) ∈ M'`.
  - Since `π` is onto `F_∞`, `π(⟨⟨M_α ∪ L(M_α)⟩⟩) = ⟨⟨π(M_α) ∪ π(L(M_α))⟩⟩_(F_∞) ⊆ M'`.
  - The base case is `π(⟨⟨R⟩⟩) = ⟨⟨π(R)⟩⟩`, and limits are unions. ✓
- **The conclusion.** For `w ∈ N ∩ F_∞`, `w = π(w) ∈ M'`. So `N ∩ F_∞ = M'` is finitely normally generated, and it is
  the relator kernel of `G_∞`.
  - `{g|_(x^p)} = G_∞`, because `π` is the identity on `F_∞` and sends `F` onto it. ✓

## 2. Linear-activity automaton (the author asked about the activity bound and faithfulness)
- **Closure.** The states are closed under sections, and all are involutions. For `ŝ_γ`, `ŝ_γ^2 = (γ^2, 1, ŝ_γ^2)`, so
  `ŝ_γ^2 = 1` for involutions `γ`.
- **Faithfulness and `Γ ≅` Grigorchuk.**
  - Every generator fixes `2` with trivial section, so `g(u2w) = g(u)2w` for `u ∈ {0,1}^*`. The action is therefore
    determined by, and faithful on, the standard action on `{0,1}^*`.
  - `ŝ_γŝ_δ = (γδ, 1, ŝ_γŝ_δ)` solves the recursion of `ŝ_(γδ)`, so `γ ↦ ŝ_γ` is a homomorphism. It is injective
    because `ŝ_γ` acts as `γ` on `0X^*`. ✓
- **(3).** The section map at `2` is idempotent with `p = 1`, and `S_∞ = {1, ŝ_a, …, ŝ_d}`. So `G_∞ ≅ Γ` is not
  finitely presented, and part 1 applies. ✓
- **(1) The activity bound.**
  - `a` is active only at the root.
  - `b, c, d` have at most 2 active vertices per level, at `1^n` and `1^(n−1)0`.
  - `ŝ_γ` is active at `2^n` and inside the cones `2^k0`, `k < n`, with at most 2 each. That gives at most `2n + 1`.
  - For `ŝ_b` this is attained up to a constant: the vertices `2^k01^(n−k−1)` are all active. So the activity is
    exactly linear. ✓
- **(2) Not contracting.** `ŝ_γ|_(2^n) = ŝ_γ` for all `n` and for infinitely many distinct `ŝ_γ ∈ G`. So no finite
  nucleus exists. ✓

## 3. Persistent subexponential automata are finite
- **(1) Two first-return walks force exponential activity.** The section graph is deterministic, so a word
  determines its walk.
  - A closed walk at `u` decomposes uniquely into first-return walks.
  - So the `2^n` block sequences of `W^(|P|)` and `P^(|W|)` give `2^n` distinct words of length `n|W||P|`, all with
    `u|_v = u ≠ 1`. That is exponential activity. ✓
- **(2) Acyclicity.** Take a cycle `O_0 ≻ … ≻ O_k = O_0`, including `k = 1`. Start at the state `u_0 ∈ O_0` that owns
  the non-`i` edge.
  - Follow the non-`i` edges and the spine edges, which connect each `θ`-orbit cyclically, back to `u_0`.
  - The first-return prefix of that walk begins with `y ≠ i`, so it differs from the spine walk, which begins with
    `i`. This contradicts (1). So heights are well defined. ✓
- **(3)** `θ̂(g) = g|_i` is an endomorphism, since everything fixes `i`, and `θ̂^M = id`, so it is an automorphism.
  - `ρ` is the wreath recursion on `X ∖ i`, a homomorphism.
  - The non-`i` sections of height-`h` states have height `< h`. Sections of products are products of letter sections,
    so `ρ(G_h) ≤ G_(h−1) ≀ Sym(X∖i)`. ✓
- **(4) Injectivity.**
  - `g(i^k yw) = i^kθ̂^k(g)(yw) = i^k yw` when `ρ(θ̂^j g) = 1` for all `j < M`, and `g(i^ω) = i^ω`. So `g` fixes every
    point of `X^ω`, hence `g = 1`.
  - Induction from `G_(−1) = 1` gives finiteness. ✓
- **The consequence** follows from the persistent-automata iff node: `V_d(G)` not finitely presented implies `G` not
  finitely presented, hence infinite, hence of exponential activity. ✓

## Nit
- **N1 (part 3, step 2).** Say explicitly that the chain walk starts at the state of `O_0` owning the non-`i` edge.
  Otherwise the walk begins with spine letters `i`, and the "begins with `y ≠ i`" argument needs that choice.
