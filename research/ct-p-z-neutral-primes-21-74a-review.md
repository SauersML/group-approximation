---
rg: 2
id: ct-p-z-neutral-primes-21-74a-review
kind: claim
title: Referee review of c9f006c0b4 (Kourovka 21.74(a) decidable on the whole positive ray, neutral primes included) — PASS; the degeneracy test of Lemma 1.2 is complete (both directions check, and the moving-holonomy search terminates), the depth bounds hold, and the radial truncation (Lemmas 2–3) preserves disjointness, cover, ĝ-invariance and nontriviality and re-applies after each prime; repairs are clarity only
distinct_from:
  ct-p-z-neutral-primes-kourovka-21-74a-is-decidable: that is the lane node under review; this checks it step by step, especially the completeness of the finite test and the core-ball truncation.
  ct-empty-z-kourovka-21-74a-is-decidable: that is the refereed V case whose Lemmas B.1, B.3 and search conditions 1–3 are imported; this checks that the new node uses them correctly and that B.3 follows from condition 2 alone.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane node by bh-2174-rank2, landed in
c9f006c0b4).** No priority claimed.
- **Read at source on origin/main:** the new node; the V node `ct-empty-z-kourovka-21-74a-is-decidable`
  (Setting, Lemmas B and C, Theorem, and bh-ref-q11's review); the positive-ray node's setting.
- **Not reviewed:** the other five files in the same commit, which apply bh-ref-d's repairs (e64cfcbeeb).
- **No code was run.**

## 1. Setting and the basic estimate: correct

- **Unit slopes.** The slopes lie in `γ^Z`, and the primes of `γ` lie in `S`. So every slope is a unit at each
  `ℓ ∉ S` and at each neutral `p`.
- **Neutral fibre maps.** A neutral piece maps `r + p^b Z_p` to `(αr + β) + p^b Z_p`, so `t = (αr + β − s)/p^b` lies
  in `Z_p` and the neutral fibre maps are isometries of `Z_p`. The node should say this in one line; it is what makes
  `β_x` an isometry in Lemma 2.
- **The estimate.** `h(c) − c = (λ − 1)(c − p)` gives the estimate.

## 2. The finite test (Lemma 1): complete

- **1.1 (degeneracy is a property of the cycle; centers are carried).**
  - `β^(N)_(gx) = β^(N+1)_x β_x^(−1)` gives the identity `(β^(N)_(gx′))^(−1) β^(N)_(gx) = β_(x′) h β_x^(−1)` with
    `h ∈ H_j`.
  - The `N = 1` holonomies fixing `q_j` say exactly that `β_x(q_j)` is independent of `x ∈ R_j`.
  - The generators of `H_(σj)` are all of this form, since `R_(σj) = g(R_j)`. So `H_(σj)` fixes `β_x(q_j)`.
  - The backward direction, using `ĝ^(−1)`, is symmetric.
- **1.2, ⇐.** Induction gives `β^(N)_x(q_j) = q_(σ^N j)` for every `x ∈ R_j`, so every holonomy of every length
  fixes `q_j`. The test only has to check `N = 1`, over finitely many pieces, refined by the neutral base classes,
  which fix `t`.
- **1.2, ⇒.** `R_i` is `g^M`-invariant, so `σ^M = id`. Iterating 1.1 shows that `β^(M)_(a_i) = C` fixes the center.
  `C` is hyperbolic, so the center is `q_i`, and 1.1 then gives the `N = 1` condition.
- **The test is per coordinate type.** For a neutral type, `q_i` is the fixed point of the neutral conjugate of `C`,
  which is also hyperbolic. The Theorem does test per type.
- **1.3 terminates.** If no generator moved `p_j`, then `H_j` would fix `p_j` and the component would be degenerate.
  Nondegeneracy is decided by 1.2 first, so the enumeration of `N` is guaranteed to stop.

## 3. Depth bounds: correct

- **Nondegenerate components.** `ψ_j` and `h ψ_j h^(−1)` lie in `H_j`, both with slope `λ_j`, and they have the
  distinct fixed points `p_j ≠ h(p_j)`. The ultrametric inequality gives `e ≤ v_ℓ(p_j − h(p_j)) + μ_ℓ`, which is
  positive for only finitely many `ℓ`.
- **(D1).** Every ball over `R_j` contains `q`. The witness `(b, q + 1, y′)` forces some part to contain `q` and
  `q + 1`, hence to have `ℓ`-component `Z_ℓ`, and then it meets `A` at `(b, q, y′)`. This is a correct
  contradiction.
- **(D2).** `v_ℓ(c − q) = v_ℓ(q) < 0`. Correct.
- **(D3).** The estimate gives "contains `q`" or "`e ≤ v_ℓ(c − q) + μ_ℓ`". This is correctly left unbounded near
  `q`.
- **Parts over two components with distinct centers `q ≠ q′`.** A ball fixed by both hyperbolic holonomies has
  `e ≤ v_ℓ(q − q′) + max μ_ℓ`. Correct.

## 4. The radial truncation (Lemmas 2–3): correct

- **Cores.** The two-center term in `E_ℓ` gives `v_ℓ(q − q′) < K`, so the cores `c_K(q)` are pairwise disjoint.
- **Lemma 2.**
  - Depth `≥ K > E_ℓ` excludes nondegenerate, D1 and D2 components. For a D3 component with center `q′ ≠ q`, a ball
    inside `c_K(q)` has `v_ℓ(c − q′) = v_ℓ(q − q′)`, so its depth is at most `E_ℓ`.
  - For every `x ∈ b_A`, including points of `U` or of other components, `β_x(D_A) = D_(ĝA)`, because `ĝA` is a
    box. `β_x(c_K(q))` is then the unique ball of radius `ℓ^(−K)` containing it, so it equals `c_K(q_(σj))` for
    every `x ∈ b_A`.
  - If `A` lies over two components with the same center `q`, the same uniqueness forces `q_(σj) = q_(σj′)`, which
    is consistent.
  - **Clarity repair 1.** "Deep at `q_(σj)`" silently needs `q_(σj)` to be a D3 center at `ℓ`. This follows:
    - `q_(σj) = β_x(q) ∈ Z_ℓ` by isometry, which rules out D2;
    - degeneracy is a cycle property, which rules out the nondegenerate case;
    - the image part has depth `≥ K ≥ 1`, which rules out D1.
    State this.
  - The non-deep ↔ non-deep claim for `ĝ^(−1)` holds by the symmetric setup.
- **Lemma 3.**
  - *Disjoint.* A non-deep ball meeting `c_K(q)` properly contains it, because balls are nested or disjoint. Then
    `(x, q, y′)` lies in both parts. Two distinct `N`'s would force equal cores.
  - *Cover.* The part `A*` through `(x, q, y′)` either contains `c_K(q)`, and then equals `A`, or lies inside it. In
    both cases it is deep-core, and `N_(A*)` covers the point. Bases are unchanged, so every member still lies
    over some `R_j`.
  - *Onto.* The fibre maps act coordinatewise. `B′_A → B′_(A″)` comes from `ĝA = A″`, and `c_K(q) → c_K(q_(σj))`
    from Lemma 2, independently of `x ∈ b_A`. So `ĝ(N_A) = N_(A″)` exactly.
  - *Nontrivial.* A proper core ball can't be the whole space, so the family is still nontrivial.
  - *Depth.* A non-deep ball through `q` contains the core, so its depth is `≤ K`. A ball missing every core has
    `v_ℓ(c − q) ≤ K − 1`, so its depth is `≤ K − 1 + max μ_ℓ`. So the stated `K + max μ_ℓ` is a valid bound, and
    the true bound is `max(K, E_ℓ, K − 1 + max μ_ℓ)`.
- **Iteration.**
  - Lemma B.3 is used again after truncation, when the family is no longer a partition. It follows from condition 2
    alone: `ĝ^N A` is a member box, and `ĝ` is fibre-preserving and bijective, so `β^(N)_x(F_A) = F_(ĝ^N A)` for
    every `x ∈ b_A`.
  - Lemma B.1 survives because bases are unchanged. The D1 argument needs only condition 1 and B.1.
  - Every constant is computed from `g`, not from the partition.
  - So truncating prime by prime is legitimate, and it never alters the components at primes already treated.

## 5. The Theorem and the example: correct

- **⇒.** After truncation the certificate is a family of candidates. Primes outside `L` are full, and radial primes
  are bounded by `B_ℓ`.
- **⇐.** This is the V argument, with canonicity on `U` as confirmed for the ray.
- **The referee's degenerate example.** It lands in case D3 with center `0`, and truncation at `K` leaves the
  permuted classes mod `ℓ`, as claimed.

## 6. Scope

- **Clarity repair 2.** The Lesson's "fibre structure is always decidable" should read "fibre structure is decidable
  once the base admits the computable flow decomposition used here". That is what the Rank-two remark says, and that
  remark is correctly labelled a sketch.

## Verdict

**PASS.**
- Kourovka 21.74(a) is decidable for every `g ∈ CT_P(Z)`, `P` finite, with slopes in `γ^Z` (`γ ≥ 2`), neutral
  primes included.
- The finite degeneracy test is complete, and the core-ball truncation is sound.
- Repairs are clarity only:
  - one line on the neutral translations `t ∈ Z_p`;
  - the D3 status of carried centers in Lemma 2;
  - the conditional wording of the Lesson.
