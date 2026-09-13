# EX review, dynamics: part 2. Later landings, refill lanes, firing sweep

Continues `research/artifacts/ex-review-dynamics-2026-09-12.md` (verdicts in §0 there) and part 1 (§§2–8).
Lane `ex-verify-dynamics`, 2026-09-13.

## 9. ex-nonsofic-action-entropy, later landings (b7acd41a75, 55c6f92ac7, cd3a1a5c40, 18dddf7c58, 8b13935ba6)

| node | verdict |
|---|---|
| `kun-thom-action-soe-class-is-rigid` (+ `-proof`); invalidates `mixing-nonsofic-action-via-soe-from-kun-thom-action` | PASS, given the Popa import. Scope note below |
| `popa-oe-superrigidity` (+ `-citation`), `popa-bernoulli-cocycle-superrigidity` | statement-level imports, not re-read here |
| `paunescu-class-closed-under-amenable-extensions` (+ `paunescu-class-amenable-extension-proof`) | PASS |
| `hyperbolic-3-manifold-groups-in-paunescu-class` (+ `-proof`) | PASS, given Agol through `fpbs-fibered-3-manifold-cost-inputs` |
| 55c6f92ac7, 18dddf7c58, 8b13935ba6 | edits to open claims and artifacts; no new establishment |

- **SOE rigidity.**
  - Popa's hypotheses hold for the generalized Bernoulli action over `K = G/Γ ⊔ G`: it is s-malleable, and
    weakly mixing because every `G`-orbit in `K` is infinite. It is free because every `g != e` moves all of
    the summand `G`. `G` is an infinite rigid subgroup of itself, w-normal and with `σ|G` weakly mixing, and
    has no finite normal subgroups (assumed).
  - Theorem 0.3 gives `n = 1/t`. For `n >= 2`, a proper invariant set for the infinite `Λ_0` rules out
    mixing. For `n = 1`, the coordinate at `Γ` is a nonconstant `Γ`-invariant function.
  - *Scope.* The import covers the diffuse base. The dead route speaks of "the Kun–Thom free action"; for
    atomic bases, s-malleability was not read at source (as the scope correction on
    `popa-bernoulli-cocycle-superrigidity` says). So the route is dead for the diffuse-base action, and the
    route body records that. No false establishment.
- **Amenable extensions.**
  - The cocycle `h(g,q) = s(gq)^-1 g s(q)` satisfies `h(g,q)s(q)^-1 = s(gq)^-1 g`, so covariance is exact.
  - The trace is exact: `gq = q` forces `g ∈ N`, and then `h(g,q) = 1` iff `g = 1`.
  - Multiplicativity fails only on `|F ∖ g'^-1F|` blocks, which is Følner-small.
  - Completing block partial permutations moves the 2-norm by `(2|F∖g^-1F|/|F|)^(1/2)`.
- **Hyperbolic 3-manifolds.** `π_1(S_g) = F_(2h) *_Z F_(2(g−h))` is in 𝒮 by Păunescu Corollary 3.7 and
  Theorem 3.9. A virtually fibered cover is surface-by-`Z`. Then finite index, Selberg, and ME for
  non-uniform lattices.

## 10. ex-rokhlin-lower, later landings (aa3a1af8ca, 5cfbc66cc5, 16138868dd), and ex-rokhlin-ascent-joint-counting (072ee83b19)

| node | verdict |
|---|---|
| `infinite-subgroup-invariant-information-has-zero-outer-entropy` (+ `-proof`) | PASS, given Seward arXiv:1804.05270 Theorem 1.2 (`koopman-lambda-singular-part-has-zero-rokhlin-entropy`) |
| `rokhlin-maximality-ascends-amenable-normal-extensions` | OPEN; route `kun-thom-wreath-maximality-from-amenable-kernel-ascent` is conditional |
| `coherent-kernel-folner-windows-force-conjugation-invariant-mean` (+ `-conjugation-mean-proof`), invalidating `amenable-kernel-ascent-via-coherent-kernel-windows` | PASS. The dead route does not fire |

- **Singularity.** A `Λ`-invariant vector of `ℓ²(G)` is `0` for infinite `Λ`. So the projection onto a
  subrepresentation embeddable in `λ` kills the spanning set. Then `F_Λ ⊆ σ-alg(H)`.
- **Coherent windows.**
  - The averaged uniform measures `μ_i` are exactly conjugation invariant and asymptotically translation
    invariant.
  - `Δ(a,b) ↦ b^-1 a` identifies `Δ\(W ×_Q W)` with `N`, with `(m,1)` acting by right translation and `(w,w)`
    by conjugation.
  - For split `W`, `Q p n r = Q (pr)(r^-1 n r)`.
  - On the Kun–Thom wreath (CIM) fails, through non-co-amenability of `G` (§5).
- **Firing.** This dead route targets the OPEN ascent claim, whose conditional route feeds the root
  `kun-thom-wreath-bernoulli-rokhlin-maximal`. Its invalidator is established by a `requires: []` proof, so
  it does not fire.

## 11. ex-tree-lattice-mixing, later landings (4581f9bd74, ec264e8a32, b0b785ed38)

| node | verdict |
|---|---|
| `burger-mozes-infinitely-transitive-tree-groups` (+ `-citation`) | import; statements match standard Burger–Mozes results, pages not re-read here |
| `nonsofic-infinitely-transitive-tree-lattice-gives-mixing` (+ `-proof`) | PASS |
| `radu-horizontal-tree-group-is-linear` (+ `-proof`) | PASS. The exact relator check is taken from the landed script output |
| OPEN `f2xf2-admits-mixing-nonsofic-action`, `nonsofic-infinitely-transitive-tree-lattice`, `radu-bmw-lattice-embeds-in-infinitely-transitive-tree-lattice`, `nonsofic-one-vertex-square-complex-group`; conditional routes | none fires |

- **Infinitely transitive transfer.**
  1. `G_i = H_i^(∞)` is closed, of finite index, hence open, and topologically simple. It is type preserving,
     since its intersection with `Aut(T)^+` is non-compact and normal.
  2. `Γ' = Γ ∩ (G_1 × G_2)` has finite index. It is cocompact, because the orbit map
     `(G_1 × G_2)/Γ' → (H_1 × H_2)/Γ` is an open and closed embedding. It is nonsofic, by
     sofic-by-finite permanence. It has dense projections, because the closure of `p_i(Γ')` is open of finite
     index, hence contains `H_i^(∞)`.
  3. `Λ_1 = p_1(Γ_(v_2))` has finite vertex stabilizers and finitely many orbits, so it is virtually free.
     A torsion-free finite-index subgroup acts freely without inversions, of rank `1 + V(p/2 − 1) >= 2`.
  4. Co-induction to `F_2 × F_2` keeps nonsoficity (Lemmas A, B), mixing (a finite twisted product of
     restrictions to the normal core), and freeness (two-coordinate graphs are null).
- **Radu's horizontal action.**
  - `m = 2u` with `g(u) = 16u^4 − 4u^3 + 4u^2 − u + 1`; Hensel gives `u ≡ 1 mod 4` and
    `−(m²+m+1) ≡ 1 mod 8`.
  - `ρ(y)/2 = [[h,−m],[1,−h]]` has determinant `(m+1)²`, a unit, so `ρ(V)` fixes `v_0`.
  - `ρ(a)`, `ρ(b)`, `ρ(c)` send `v_0` to the neighbours `[0:1]`, `[1:0]`, `[1:1]`.
  - The map from the Cayley tree of `C_2 * C_2 * C_2` is a covering of trees, hence an isomorphism.
  - The orders `192 → 1536` give `(H ∩ K_3)K_4 = K_3`. Squaring lifts, since `2j >= j + 2`, so `H >= K_3`
    and the index is `384/192 = 2`.
  - `tr²/det ρ(xy) = 4(m²+m+1)/(m+1)²`, with `2cos θ` a root of `2t² + t − 2`, not an algebraic integer, so
    `ρ(xy)` has infinite order and `Λ_v` is infinitely generated.
  - `QZ` of an open subgroup of `PGL_2(Q_2)` is trivial, so the vertical action is faithful.
  - Consistency with Titz Mite–Witzel: from `f(m) = 0`, `t = m + 1/m` satisfies `2t² − t − 2 = 0`.

## 12. ex-lattice-space-action, later landings (6d94d7b74b, 31625a5f8c, e3dd844bba)

| node | verdict |
|---|---|
| `sl3-split-class-lattice-quotient-actions-are-sofic` (+ `-proof`) | PASS |
| OPEN `sl3z-on-cocompact-lattice-quotient-is-not-sofic`; routes `sl3z-nonsofic-action-from-cocompact-lattice-quotient`, `mixing-nonsofic-action-from-sl3z-cocompact-quotient` | no false establishment. The "strongest form" paragraph is marked as a heuristic |

- **Split class.**
  - (F) factors and (R) restriction are restrictions of the embedding.
  - (D) duality: the coupling `(γ_1,γ_2)·g = γ_1 g γ_2^-1` with SOE invariance, plus freeness via proper
    centralizers.
  - (C) conjugation: `xΓ_2 ↦ h^-1 x k (k^-1 Γ_2 k)`.
  - The seven steps through `Γ_0 = Γ ∩ Γ_1 ∩ Γ_2` are valid.

## 13. ex-bernoulli-rokhlin-complete (a091c1f300, 71a738c65d), ex-bernoulli-zero-supremum (e619b92974, b38ee6bf9a, 0bb801a234)

| node | verdict |
|---|---|
| `iid-generators-not-dense-at-positive-rokhlin-supremum` (+ `-proof`) | PASS, given the Seward II imports |
| `nonamenable-bernoulli-shifts-are-weakly-isomorphic` (+ `-citation`) | PASS. Bowen arXiv:1707.09573v4 Corollary 1.3 verbatim (text line 124) |
| `zero-supremum-collapse-via-dense-iid-generators` (route, conditional) | PASS. Density alone already gives a generating element, so the Baire step is redundant but valid |
| `generators-dense-iff-zero-rokhlin-entropy` (+ `-proof`) | PASS |
| `seward-small-support-relative-generators` (+ `-citation`) | PASS. arXiv:1405.3604 Lemma 2.2 (text line 390) and Theorem 2.3 (line 422) match verbatim |
| `bernoulli-infinite-power-iff-approximate-half-absorption` (+ `-proof`) | PASS |
| `rigid-actions-have-no-dbar-close-bernoulli-models` (+ `-proof`) | PASS |
| `bernoulli-measures-not-finitely-determined-at-zero-supremum` (+ `-sup-proof`), cce47a6658 | PASS |
| `seward-bernoulli-measures-finitely-determined-under-rbs` (+ `-citation`) | PASS. arXiv:1804.05269v3 Corollary 1.6 (text line 281) and the convention that `h_G` is Rokhlin entropy (line 148) match verbatim |
| OPEN `iid-generators-dense-at-zero-rokhlin-supremum`, `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`, `zero-rokhlin-supremum-forces-bernoulli-collapse` | still OPEN; edits add attempts only |

- **Not dense at positive supremum.**
  - Item 1 is two-step subadditivity: `r <= min(a,s) + ε + H(γ|𝒜)`.
  - Item 3 is Fano, `H(γ|ξ) <= h_2(δ) + δ log(|L|−1)`.
  - Item 4: continuity of `H_ν(ℓ|(𝒫_A')^W)` on the joining space, and Step 1 applied inside a determined
    joining, give `r_λ < r_λ`.
- **Generator density.**
  - `μ(R)H_(μ_R)(β) <= Nφ(r) + ε/8`.
  - Theorem 2.3 gives a generating pre-partition of measure `r`, and Lemma 2.2 extends it.
  - `H(α|β) <= h_2(r) + r log 2` and `H(β|α) < ε/2`.
- **Half absorption.**
  - The capture step gives `μ(U Δ U') <= |R|δ`, because the atoms of `P` are disjoint.
  - `A_∞ = ∨ A_n` contains every `B_j`, hence is `B_X`.
  - (1)⇒(2) splits the coordinates into `{0..n−1} ∪ {n, n+2, …}` and `{n+1, n+3, …}`.
- **Rigid actions.** `c_λ <= 2d + ν(x(g_n) != x(1))`. Hosts: left translation on the closure of `ι(G)` in a
  compact group, which is free, ergodic and rigid, because an infinite compact group has no isolated point.
- **Not finitely determined at zero supremum.**
  - A rigid free ergodic `X` has `h^Rok(X) = 0`: infinite would force `s > 0`, and finite means at most `s`.
  - Models `ν ≅ X` approach `λ^G` weak* (threshold item 1), with equal entropy `0` and the same free
    stabilizer type, while `d̄(ν, λ^G) >= c_λ/2`. So `ε = c_λ/4` defeats every `(U, δ)`.

## 14. Firing sweep (135 nodes landed by the eight original lanes; refills in §§10, 13)

- **`requires: []` routes: 18.**
  - 8 citations: Alpeev–Seward, Burger–Mozes, Cordeiro, Ciobotaru, Bowen, Păunescu 1.5, Seward II §6, Popa.
  - 6 complete proofs, all re-derived above.
  - 4 dead routes, each with an invalidator established through `requires: []` chains:
    - `leavitt-induced-absorption-gives-bernoulli-collapse` ← `finite-subgroup-induced-absorption-conserves-entropy` ← lifted trace;
    - `mixing-nonsofic-action-via-permutation-centralizers` ← `permutation-centralizer-blind-to-weakly-mixing-actions`;
    - `mixing-nonsofic-action-via-weak-containment-of-kun-thom-action` ← `weak-containment-is-blind-to-kazhdan-fixed-algebras`;
    - `mixing-nonsofic-action-via-soe-from-kun-thom-action` ← `kun-thom-action-soe-class-is-rigid` ← `popa-oe-superrigidity-citation`, `kun-thom-nonsofic-wreath-citation`.
- **Other dead routes into the same roots.**
  - `mixing-nonsofic-action-via-fixed-algebras` ← `kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions`
    ← `kazhdan-projection-norm-limit-of-averages-proof` (`requires: []`).
  - `amenable-kernel-ascent-via-coherent-kernel-windows` (§10).
- **No prose-only establishment, and no id over 64 characters.**
- **Routes into the famous roots.** Covered: the Bernoulli classification pair, POS, RBS maximality, the
  Kun–Thom wreath root, the mixing root, `sl3z-admits-nonsofic-action`, the F2×F2 claims, the zero-supremum
  and above-supremum claims, and the ascent claim. Of 36 routes, every one with nonempty `requires` has at
  least one prerequisite that is not ESTABLISHED. So none of these roots is established, falsely or
  otherwise.
- **Out of scope.** The `ex-cubic-division-strong-convergence` nodes (9be1729418) are about strong convergence
  of congruence representations, which is operator-algebraic, and were not reviewed here.
