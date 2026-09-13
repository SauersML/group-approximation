# EX review, wave 2, part 5: wave-2 census, strict compression, and the amenable-action lane (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tips `6de47b9ab` to `0f57d3cdf`.

## 0. Census additions and corrections

**Wave-2 lanes added by the coordinator (12).** ex2-sl3z-cocompact-weak-containment, ex2-dyadic-vertex-action,
ex2-labbe-lef-crux, ex2-labbe-relation-climbing, ex2-labbe-quantum-rigidity, ex2-radu-chain-lamp-positive,
ex2-radu-superstrong-negative, ex2-triangle-persistence, ex2-weak-sofic-bounded-factors, ex2-weak-sofic-affine-targets,
ex2-free-wreath-amenable-sofic, ex2-q34-commuting-units.
- The landing log gives 80 research paths: 45 claims and 35 routes. ex2-labbe-lef-crux has landed no research node.
- 25 claims carry ESTABLISHED. Three triangle-persistence nodes are established through a route without a status line.
- `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups` already PASSes in
  `ex-review2-dynamics-2026-09-13-part3.md` §3.1, so it is dropped.

| priority | lane | established claims |
|---|---|---|
| famous or refuting | free-wreath-amenable-sofic | `amenable-action-of-a-sofic-group-need-not-be-sofic`, `free-wreath-over-an-amenable-action-can-be-nonsofic`, `co-amenable-induction-of-sofic-actions`, `compiler-rope-edge-is-not-co-amenable`, `separating-sofic-quotient-sets-make-an-action-sofic` |
| famous or refuting | labbe-quantum-rigidity, labbe-relation-climbing | `periodic-quantum-tilings-refute-quantum-rigidity`, `sft-wall-rigidity-iff-idempotent-commutator-ideal`, `zd-derived-full-group-fp-excludes-periodic-quantum-tilings` |
| reductions | radu-chain-lamp-positive, radu-superstrong-negative | `radu-delta-squared-orbit-is-signed-permutation-module`, `radu-metabelian-quotient-embeds-in-edge-lamp-wreath`, `radu-square-lamp-forces-reflections-in-finite-actions` |
| reductions | sl3z-cocompact-weak-containment | `sl3z-cocompact-not-factor-of-bernoulli-times-profinite`, `ioana-profinite-cocycle-superrigidity` (citation), `popa-bernoulli-product-cocycles-come-from-cofactor` (citation) |
| reductions | dyadic-vertex-action | `expanding-matchings-need-a-shared-stabilizer`, `homogeneous-quotient-soficity-gives-vertex-soficity`, `twin-deep-vertex-models-give-homogeneous-microstates` |
| reductions | weak-sofic-affine-targets, weak-sofic-bounded-factors | `hensel-covering-of-nilpotent-kernels-by-commutators`, `relator-width-over-transitive-abelian-extensions`, `simple-group-width-over-congruence-targets`, `relator-width-survives-abelian-and-central-extensions` |
| rest | triangle-persistence | `sl2-opposite-root-subgroups-codistance-inverse-sqrt-q`, `sl2-subfield-root-links-codistance-q8-q16`, `sl2-subfield-root-pair-girth-eight`; route-only `coset-graph-singular-values-bound-fixed-space-angles`, `kassabov-subspace-angle-criterion`, `triangle-of-groups-half-girth-structure` |

**Wave-1 correction (from ex-verify-groups).** Six items of part 4 already had a PASS whose section headings do not
spell out the id. So part 4 is an independent second pass on each of them:
- `thompson-f-sofic-iff-relator-system-unstable` and `thompson-f-hyperlinear-iff-relator-system-hs-unstable` (groups
  part 3 §3.1);
- `non-rf-hyperbolic-group-or-unique-product-nonsofic-group` and `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group`
  (part 2 §2.2);
- `relatively-kazhdan-amenable-pairs-allow-sofic-defects` (part 8 §8.5);
- `ollivier-wise-kazhdan-rips-construction` (part 16 §16.2).

The backlog lane confirms that its §27.1 did not re-derive Lemma 2.1's span claim, and part 2 §2 did.

## 1. Coordinator priority: `strict-one-sided-compression-forces-infinite-bi-index`

- **Graph state.** The node (06bd3589a, 2026-08-30) had no route. ex-complexity-sofic-amplifier landed
  `strict-one-sided-compression-forces-infinite-bi-index-proof` in 6a80e95f3. That route has `requires: []` and gives
  a complete derivation in plain notation. It matches mine step for step, so no second route was landed.
- **cairn why** (MSI, private shared clone at `0f57d3cdf`, empty `CAIRN_STATE`):
  - the target computes ESTABLISHED via its direct proof;
  - `machine-center-amplifier-target-not-finitely-presented` computes ESTABLISHED via
    `machine-center-amplifier-target-not-fp-proof`;
  - `machine-center-amplifier-does-not-bypass-the-sofic-compiler` computes ESTABLISHED via
    `amplifier-compiler-domination-proof`.
  - Every node in both derivation trees is ✓.

## 2. The strict compression theorem: PASS on (SCI1)--(SCI6)

- **(SCI4).** Conjugation by `t^(k-1)` preserves strict inclusion, so `t^k H t^(-k) < t^(k-1) H t^(-(k-1)) <= H`.
- **(SCI3).** `h t^(-n) h' = t^(-n)(t^n h t^(-n))h' in t^(-n)H`, so `H t^(-n) H = t^(-n) H`.
- **Distinctness.** `t^(-m)H = t^(-n)H` with `m > n` gives `t^(m-n) in H`, hence `t^k H t^(-k) = H`. That contradicts
  (SCI4). The double cosets are distinct sets, hence distinct double cosets, so (SCI2) follows.
- **(SCI5).** If `P_H` generates `G` and every element of `P_H` normalizes `H`, then `G` normalizes `H`.
- **(SCI6), from the arXiv:2608.02025v2 PDF, p. 3.**
  - `P ⊇ P_1 × P_2 × S`, and `u_i` conjugates `P` onto `P_i`. So `t_1 Γ t_1^(-1) = π(P_1)`, with `Γ = π(P)`.
  - `[P_1, S] = 1`, so an element of `π(P_1) ∩ π(S)` is central in `π(S) ≅ S`. `S` is simple with trivial centre,
    so the intersection is trivial.
  - `1 != π(S) <= Γ`, so `t_1 Γ t_1^(-1) != Γ`. Strict.
- **Display.** The node's TeX escapes are damaged. A review line pointing to the route was landed on the node.

## 3. ex2-free-wreath-amenable-sofic: all five PASS

**`amenable-action-of-a-sofic-group-need-not-be-sofic`.**
- *(A1).* `⊕ G_n` is a directed union of residually finite groups, and the `Z`-extension keeps soficity.
- *(A2).*
  - The points `x_m = t^m K` are distinct, because `K` has no `t`-component.
  - For `m <= -1`, `Stab(x_m) = Γ_m × ⊕_(n >= m+1) G_n ⊇ G_0`.
  - The window measures satisfy `||g_* mu_N - mu_N||_1 <= 2|g|/N`, by telescoping over the letters. A weak-*
    cluster point is an invariant mean.
- *(A4).* `G_0 ∩ K = Γ_0`, so `O = G_0 x_0 ≅ G/Γ`, and `(⊕_O Z/2) ⋊ G_0 ≅ (Z/2) wr_(G/Γ) G`. That group is nonsofic by
  Kun--Thom Theorem A (v3 PDF, p. 2, verbatim).
- *(A3).* GKP Theorem A (arXiv:2401.04945, verbatim) turns a sofic `H ↷ X` into a sofic `(Z/2) wr_X H`, a contradiction.
- *Scope.* Gruenberg's criterion makes `G wr Z` non-residually-finite, because `G` is nonabelian.

**`free-wreath-over-an-amenable-action-can-be-nonsofic`.**
- *Step 1.* A subfamily of free factors generates its own free product, by a retraction. So
  `W_O = (*_O Z) ⋊ G_0 ≅ <G, v | [v, Γ] = 1>`.
- *Step 2.* In `G *_Γ (Γ × <v>)`, the image `a_1 v b_1 v^(-1) a_2 ...` of a reduced word of `G *_Γ G` alternates between
  `G \ Γ` and `(Γ × <v>) \ Γ`. It is reduced, hence nontrivial. The edge cases (a single letter from the second copy,
  or a word beginning or ending with one) come out reduced as well.
- *Step 3.* The group double `G *_Γ G` is nonsofic (Kun--Thom Theorem A), and soficity passes to subgroups.

**`co-amenable-induction-of-sofic-actions`.**
- *The cocycle.* `c(g,x) = σ(gx)^(-1) g σ(x)` fixes `x_0`, and the identity
  `c(gh,x) = c(g,hx) c(h,x)` holds by insertion of `σ(hx) σ(hx)^(-1)`.
- *Følner set.* `x in T \ T_0` lies in `T \ g^(-1)T` for some `g in F_2`, and `|T \ g^(-1)T| <= |gT Δ T|`.
- *Multiplicativity.* On `T_0 × B`, both composites have first coordinate `ghx in T`, and their `B`-coordinates use
  `c(g,hx), c(h,x), c(gh,x) in F_K`. So the defect is `< |T \ T_0|/|T| + δ < 2δ < ε`.
- *Labels.* `z = σ(gx)^(-1) y in E'` and `k^(-1) z = σ(x)^(-1) g^(-1) y in E'`. The stabilizer model's equivariance
  applies at `b in S_B` with `ψ(k)b in S_B`, and gives `π_(φ(g)s)(y) = π_s(g^(-1) y)`.
- *Novelty.* The node checked only GKP arXiv:2401.04945. Their graph-action paper arXiv:2408.15470 (Theorem 1.7, amenable
  stabilizers, transitive actions) is a different statement. I did not check whether it contains this theorem.

**`compiler-rope-edge-is-not-co-amenable`.**
- *(R1).* `F/(F ∩ core L) ↪ K/core L`, and it maps onto `F/N`.
- *(R2).*
  - The coset space `F(X_e)^2 / M_e ≅ H_e` via `(u,v) ↦ φ(u)φ(v)^(-1)`, which I checked is well defined and bijective.
  - A `K_e`-invariant mean pushes forward, and restricted to `F(X_e) × 1` it gives a left-invariant mean on `H_e`.
    But `H_e ⊇ Q_e ⊇ F(x,y)`, so no such mean exists.
- *(R3).* `L_e = L_e^0 × L^g`, so the coset action is a product. (S2) applies. The graph of a homomorphism into a
  residually finite group is separable.

**`separating-sofic-quotient-sets-make-an-action-sofic`.**
- *(S1)* and *(S2)* are checked as written.
- *(C1) and (C2).* For each pair in `E`, some `K_i` separates. Then `K' = ∩` of finitely many `K_i` gives an
  equivariant map injective on `E`, and `core(K') = ∩ core(K_i)`.
- *(C3).* `M_i = {(u,v) : uv^(-1) in N_i}` is a subgroup, since `N_i` is normal. It contains `N_i × N_i`, and
  `∩ M_i = M_Q`.

**Imports consumed, not re-derived here.**
- The GKP toolkit nodes (Proposition 2.15, Theorems 2.17 and 3.7) and `centralizer-hnn-is-free-generalized-wreath`.
- Of the GKP statements, only Theorem A was re-read, verbatim.

## 4. Verdicts

| claim | verdict |
|---|---|
| `strict-one-sided-compression-forces-infinite-bi-index` | PASS on (SCI1)--(SCI6) |
| the five ex2-free-wreath-amenable-sofic claims | PASS; novelty of the co-amenable induction theorem checked against arXiv:2401.04945 only |

Next parts: labbe quantum rigidity and relation climbing, radu, sl3z, dyadic vertex action, weak-sofic targets, then
triangle persistence.
