# Adversarial review: swarm-6 group theory, Boone–Higman and percolation claims (2026-09-12)

Reviewer lane `swarm6-reviewer-groups` (swarm 7). The scope is the ESTABLISHED claims that swarm 6 landed
after 17:00 in group theory, Boone–Higman and percolation, plus 2bc488e31, which was added to the queue after
the 20:11 restart.
- Tips read: b17de6526 for the first pass, a64c47375 after the restart.
- Verdicts are PASS, FAIL or GAP. "Source not re-read" marks an import whose source this lane did not open.

## 0. Skipped: a verdict is already recorded

- `birman-sequence-genus-three-does-not-virtually-split` has its own reviewer (`review-birman-genus3-2026-09-12.md`).
- `regular-tree-torsion-orders-have-primes-at-most-degree` and `cycle-transposition-lef-group-has-no-regular-tree-action`:
  `review-swarm4` §29.3 and §29.4.
- `baumslag-gersten-base-is-elliptic-in-every-tree-action` and `magnus-hnn-permanence-forces-one-relator-boone-higman`:
  `review-swarm4`, both PASS.
- `kl-three-coincidence-residue-words-inject-with-room-for-loops` and
  `kl-involution-loop-residue-with-interior-light-label-injects`: `review-swarm4` §29.8.
- These five verdicts landed in `review-swarm4` while this lane was reading the same nodes. This lane's own
  reads also give PASS, and add the following points.
  - **`fpbs-central-amenable-relative-threshold-is-pu`** (§34.2). The import `fpbs-amenable-wq-normal-pu-is-relative-pc`
    and its route ask only that `H` be infinite, amenable and wq-normal. They never ask that `H` be finitely
    generated, so `J = AC` qualifies even if it is infinitely generated.
  - **`relative-pbh-closed-under-finite-direct-products`** (§34.3). The kernel identity in part 1 needs both `S_i`
    nonempty, and the route says so.
  - **`baumslag-char-zero-metabelian-group-is-not-self-similar`.** In case (a), `U = -g` and `V = 1+g` are units
    whose zeros and poles lie in `{0,-1,∞}`. Mason–Stothers gives `deg U ≤ 1`, and the six maps are the
    anharmonic group of that triple. The step `λ ∈ R` uses that `R/pR` is a domain, which holds.
  - **`acyclic-quotientless-extension-completion-is-kernel-completion` and `leavitt-kazhdan-cover-rf-iff-kernel-rf`**
    (§38.1). No further points.

## 1. `aut-out-free-abelianized-extension-splits-rationally` (67f49fd18): PASS

The standard spectral-sequence input was not re-read.
- **Crossed homomorphism.**
  - The Fox chain rule gives `M(φψ) = φ(M(ψ)) M(φ)` for abelianized Jacobians.
  - The units of `Z[Z^n]` are `± monomials`, so the exponent of the determinant is a crossed homomorphism
    `h: Aut(F_n) → Z^n`.
- **Inner automorphisms.**
  - `∂(g x_k g⁻¹)/∂x_i` abelianizes to `t δ_ki + (1 − t_k) v_i`, so the Jacobian is `tI + u v^T`.
  - The fundamental formula `Σ v_i (t_i − 1) = t − 1` gives `v^T u = 1 − t`.
  - So `det = t^{n−1}(t + v^T u) = t^{n−1}`, and `h(ι_g) = (n − 1)[g]`.
- **The extension class.**
  - `h|Inn` is a homomorphism, so `h` descends through `[Inn, Inn]`.
  - A crossed homomorphism that restricts to `(n − 1)·id` on the kernel kills `(n − 1)c`.
  - Sanity check: at `n = 2` this gives `c = 0`.
- **Injectivity of `π^*` rationally.**
  - In the two-row LHS sequence, `ker π^* = im d_2`.
  - Rows 0 and 1 agree with those of the abelianized extension, by naturality and `H^1(F_n; M) = Hom(H, M)`.
  - In degree 0 there is a direct check: `f ∘ h/(n − 1)` extends `f` to a crossed homomorphism.
  - In general `d_2` is cup product with `c` (Hochschild–Serre, Charlap–Vasquez; source not re-read). On
    `Q`-modules it vanishes because `n − 1` is invertible.

## 2. `free-splitting-fa-lifts-choose-a-side` (67f49fd18): FAIL as stated, corrected forward by narrowing scope

**The literal statement is false.** The Setting puts no size condition on `Λ = Γ ∩ J_B`.
- **`Γ = 1`.**
  - `Λ = 1` has FA and finite abelianization.
  - `s(Λ)` fixes all of `T`. The formula in (S) holds for every `x`, but the fixed tree is not a star, and (N)
    fails too. So "exactly one of (S), (N)" is false.
- **A nontrivial finite `Λ`.**
  - Take `rank B ≥ 3` with basis `b_1, b_2, b_3, …`, and let `β` swap `b_1, b_2` and fix the rest.
  - Let `Γ = ⟨[id ∗ β]⟩ ≅ Z/2`, with `s([id ∗ β]) = id ∗ β`.
  - The fixed tree contains `⟨p⟩`, `pB` and `b_3⟨p⟩`. The last two are at distance 3, so the fixed tree is
    not the star of any `⟨p⟩`-vertex, and it is not a single vertex.

**The hidden hypothesis.** Step 4 of the route says that the fixed `⟨p⟩`-vertices satisfy
`(id ∗ β)(x) ∈ x⟨p⟩` "for all `β` in a finite-index subgroup of `Aut(B)`". That needs `[J_B : Λ] < ∞`.

**With `[J_B : Λ] < ∞` the claim holds.**
- **Fixed tree of the standard lift.**
  - A neighbour `p^m b⟨p⟩` of `p^m B` is fixed exactly when `β(b) = b` for every `β_λ`.
  - A finite-index subgroup of `Aut(B)` contains `ι_{c^k}` for every `c ∈ B` and a fixed `k`. So such a `b`
    commutes with every `c^k`, and `b = 1` since `rank B ≥ 2`.
  - Fixed sets are subtrees, so the fixed tree is exactly the star. This also supplies the unproved step
    "forces `x ∈ ⟨p⟩`".
- **The rest of the route is correct.**
  - Injectivity of `J_B`.
  - The action formula, with no inversions.
  - FA gives a fixed vertex.
  - In case (S), `y` is a homomorphism to `Z`, which is trivial by finite abelianization.
  - In case (N), the fixed tree has no edge, `y` is a cocycle, and `ρ` is a homomorphism.
- **Nothing downstream is lost.**
  - The node's "When the hypothesis holds" concerns finite-index `Γ` with `n ≥ 5`, and for those
    `[J_B : Λ] < ∞` is automatic.
  - Such a `Λ` has finite index in `Aut(F_{n−1})`, which has (T) for `n − 1 ≥ 4`. So `Λ` has FA and finite
    abelianization.

**Correction.** The node's Setting now requires `Λ` to have finite index in `J_B`, and records the two
examples above.

## 3. `fpbs-twisted-level-percolation-disconnected-at-low-density` (6c78684d0): PASS, with a degenerate GAP corrected forward

- **Definitions.** The random graph agrees with item 2 of `fpbs-twisted-level-graph-generates-cyclic-extension`.
  Open pairs `(u, m)` are i.i.d. with probability `δ`, and they give edges `{u, φ^{−m}(x) u}` with
  `φ^{−m}(x) = t^{−m} x t^m`.
- **Step 1.**
  - `E(t) = ⟨t⟩`, since a root `w` of `t` would map to `±1/k` in `Z`.
  - `⟨t⟩ ∩ N = e`, and `m ↦ t^{−m} x t^m` is injective.
- **Steps 2–3.**
  - Each edge has at most `2|S|` witnessing pairs.
  - A pair witnesses at most two edges of a self-avoiding path, so at least `l/2` distinct pairs must be open.
    The union bound then carries `δ^{l/2}`.
- **Step 4.**
  - The cycle word is `t^{−m_l} x_l t^{m_l − m_{l−1}} ⋯ x_1 t^{m_1} s^{−1}`, of length at most `2(l + 1)`.
  - Its `t`-components lie in the cosets `s w_i^{−1} ⟨t⟩`. These are distinct by self-avoidance and
    `⟨t⟩ ∩ N = e`, so every component is isolated. Zero exponents simply drop out.
  - The count `2^{(K+2)(l+1)}` of exponent vectors is correct.
- **Steps 5–6.**
  - The series is below 1 for small `δ`.
  - Bernoulli percolation over the free `N`-action with infinite orbits is mixing. "Connected" is an invariant
    event, so its probability is 0.
- **GAP: `N = 1`.**
  - Then `Γ = Z` is torsion-free hyperbolic and `S ⊆ N ∖ {e}` is empty. `T_δ` is a single vertex, which is
    connected, so item 2 fails.
  - The fix is to assume `N ≠ 1`. Then `N` is infinite, because `Γ` is torsion-free, and the proof applies.
  - The node's Setting now says so.
- **Imports.**
  - For Osin's Lemma 2.27 see §4.
  - `hyperbolic-group-relative-to-maximal-elementary-subgroup` was not re-read.
