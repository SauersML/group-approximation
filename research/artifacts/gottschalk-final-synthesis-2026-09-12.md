# Gottschalk surjunctivity: final synthesis of the team region

Date: 2026-09-12 (wrap-up). Lane `w3-strategist-gate`. Main was at `4ca24765ad` when this was drafted, and later
landings are folded in where noted.

This artifact extends two earlier ones:
- `research/artifacts/gottschalk-region-synthesis-2026-09-12.md` (54b9d7b704);
- the gate plan `research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md` (ede445b316).

It changes no node's status. It records where the team stopped.

**Status words used below.**
- **Verified.** A verifier section re-derived the result and passed it. Cited as `<verifier> §N`.
- **Graph.** The node is ESTABLISHED on main, but this synthesis did not trace a verifier section for it.
- **Paper.** A complete argument is landed and the node is held OPEN. Verification is requested in the commit message
  of this landing.
- **Dead.** A verified obstruction or refutation kills the route as stated.

**Verifier artifacts.** Each lives at `research/artifacts/<name>-verification-2026-09-12.md`, except the last, which is
`research/artifacts/gottschalk-negative-side-verification-2026-09-12.md`.

| verifier | commit used | scope |
|---|---|---|
| gk-vf-chain | 8b685e2f95 | corner ⟺ Rep_p chains, binary and ternary |
| gk-vf-gate | 89d646844c | R4 and SUB gate family, §1–37 |
| gk-vf-linear-b | b504f6fba2 | linear side, Clifford, Deligne, Radu, weakly finite chain, matrix states, §0–42 |
| gk-vf-linear | 64a50c8714 | linear side, two-root identity, characteristic 3 scope |
| gk-vf-nonlinear | 724cfbfae5 | formalizability, Kun–Thom witnesses, VH lattices |
| gk-vf-positive | c2a5a4a777 | Bernoulli, Kazhdan, wreath closures |
| gk-vf-positive-b | 91a473dd33 | linear sofic rung, coset shifts, subshift tracks |
| w3-vf-linear | 4eb654892a | rank functions on Thompson's V, the ternary V gate, §1–34.7 |
| w3-vf-nonlinear | 83970f5256 | host roots: Clifford, Radu, Higman, lamps, 2V, §1–31 |
| w3-vf-positive | 893890d7a1 | weak soficity, Deligne p-subgroups, products |
| gottschalk-negative-side | 3f71a3a507 | Garden-of-Eden localization, Kaplansky normal forms |

## 0. The goal

`gottschalk-surjunctivity-conjecture` says: for every group `G` and finite alphabet `A`, every injective cellular
automaton `A^G -> A^G` is surjective.
- **Status: OPEN in both directions.**
- All ten of its `refuted_by` roots are OPEN, and an ESTABLISHED root would refute the goal.
- No candidate proof of the goal exists. The positive side holds reductions and filters only.

**Where it stopped.**
- Every linear route ends at a lifting problem: a one-sided inverse pair in a matrix ring over a group algebra. The
  verified chain rewrites this as the absence of weakly finite representations.
- Every nonlinear route ends at a design problem with no candidate automaton.
- No route crossed either wall.

**Global results.**
- **Linear criterion.** `stable-finiteness-failure-refutes-surjunctivity`: if `M_n(k[G])` is not directly finite for
  some finite field `k`, then `G` is not surjunctive.
- **Reduction (graph).** `gottschalk-reduces-to-fg-simple-kazhdan-groups`: the conjecture holds for an alphabet iff it
  holds on finitely generated simple Kazhdan groups.
- **Evasion (graph).** `gottschalk-counterexamples-lie-outside-the-permanence-closure`: a counterexample lies outside
  the closure of the sofic groups under every available permanence theorem.
- **Tables (graph).** `strict-pairs-transfer-to-table-realizations`: a certificate's product tables must fold its
  orphan cells under every homomorphism into a finite or surjunctive group.
- **Algebraic subshifts (graph).** `full-shift-maps-into-two-sided-algebraic-subshifts-are-constant`: no construction
  passes through the dual of the Leavitt algebra.
- **No Kazhdan rounding (graph).** `kazhdan-group-rank-models-admit-no-expander-decomposition`: property (T) gives no
  rank rounding.
- **Trees (graph).** `end-fixing-tree-symmetries-carry-strict-automata`.
- **Nonsofic hosts.** `d-ary-leavitt-groups-nonsofic-over-finite-fields` (the claim text records ESTABLISHED, Lean
  `Leavitt/AryEndpoints`) and `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`. So Gromov–Weiss decides no
  Leavitt host.
- **The corner chain (verified).**
  - Rep_p means that every homomorphism from `F_p[G]` into a weakly finite ring factors through the augmentation.
  - The chain reads: corner fullness ⟺ Rep_p ⟺ `J_omega = omega` ⟹ `J_1 != 0` ⟹ `G` is nonsurjunctive.
  - Binary, unconditional: gk-vf-chain §2. Ternary, conditional on simplicity of `PG` (Khanh, arXiv:2609.08428v1):
    gk-vf-chain §3. The lane landings are a64c47375f and e122985617.
  - gk-vf-chain §4: neither converse link is proved. Those links are Gott_p ⟹ SF_p and SF_p ⟹ Rep_p. **Never read the
    chain as "counterexample ⟺ no weakly finite representation".**

**Positive side.**
- **OPEN targets:**
  - `every-injective-ca-preserves-uniform-bernoulli-measure`
  - `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`
  - `leavitt-units-have-zero-rokhlin-entropy-supremum`
  - `leavitt-units-are-not-quantitatively-surjunctive`
- **Paper:**
  - `bernoulli-per-copy-rokhlin-entropy-is-zero-or-full` (286ccdcb36, w7-rokhlin-dichotomy): the zero-or-full collapse,
    with no floor on V.
  - `zero-rokhlin-supremum-forces-bernoulli-collapse` (9c34e9e7f5): the bridge claim.
- **Graph.** `factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy` (a564fb2cfc).
- **Verified.** Injections into subshift tracks lower Bernoulli Rokhlin entropy (d58fa0f323): gk-vf-positive-b §11.

## 1. Root by root

### 1.1 `leavitt-unit-group-nonsurjunctive` (binary: `G = L_(F_2)(1,2)^x`)

**Verified.**
- **Corner ⟺ Rep_2**, unconditional: gk-vf-chain §2.
- **Rank functions and corners** (gk-vf-linear-b):
  - §10: `simple-group-rank-functions-are-augmentation-or-detecting`;
  - §13: the routes into Kaplansky failure;
  - §32: the binary cyclic corner and its complement;
  - §34: the swap split at the central involution;
  - §35: weakly finite representations of the binary corner.
- **Sylvester exact globality and kernel compressions** in characteristic 2 (w7-sylv-global): gk-vf-linear-b §39,
  ae0a4005ef. `sylvester-disjoint-cylinder-defects-strictly-submultiplicative` stays OPEN.
- **Thompson's V inside `G`.**
  - The nodes are `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups` and
    `v-rank-order-char-cycles-are-trivial-plus-regular`, both established at f0b103bb41.
  - Verifiers: w3-vf-linear §32 (87e69e1510) and §33 (5e04d5570b).
  - On every finite `H <= V`: `rk = phi_V rk_aug + (1 - phi_V) rk_reg`. So the V gate is `phi_V in {0, 1}`.
- **No unstable K_2 at rank three.** `leavitt-unit-groups-have-no-unstable-k2-at-rank-three`: gk-vf-gate §34
  (b55d89486d). The lane landing is 8afa079662 and the status change is e785a89eda.
- **`leavitt-prime-field-units-generated-by-v-and-one-transvection`:** gk-vf-gate §27.
- **The R4 inputs**, gk-vf-gate §2–35: see Section 2.

**Paper.**
- **w7-el3j-presentation** (8fc212cf45). The claims are:
  - `jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel`
  - `jacobson-el3-amalgam-kernel-is-residually-finite`
  - `toeplitz-commutators-do-not-normally-generate-amalgam-kernel`
  - `binary-jacobson-el3-is-finitely-presented`
  - `jacobson-el4-is-finitely-presented-steinberg-group`

  `binary-jacobson-el3-is-sofic` stays OPEN with no candidate.
- **Presentations of `G`** (lane `ex-free-objects`, unreviewed, outside the team):
  - V plus one involution, in `research/artifacts/thompson-steinberg-presentation-2026-09-12.md` (14a3ca5645);
  - seven generators and sixty relators (0f2758222e).

**Dead.**
- The R4 reduction, Plan 1, unitriangular data, halving, the K_2(3,R) option, and the averaging and Hamming
  extensions: see Section 2.
- Binary formalizability is false (family F): gk-vf-nonlinear §24.

**Where it stops.**
- The open lift is `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` (OPEN), equivalently Rep_2.
- `thompson-v-nonsurjunctive` (OPEN) would imply this root, because nonsurjunctivity ascends from `V <= G`.

### 1.2 `ternary-leavitt-unit-group-nonsurjunctive` (`G = L_(F_3)(1,2)^x`, `z = -1`, `S_- = eps_- F_3[G]`)

**Verified.**
- **Corner ⟺ Rep_3**, conditional on simplicity of `PG`: gk-vf-chain §3.
- **The weakly finite representation chain** (gk-vf-linear-b §28, §29, §36, §37, §38):
  - `weakly-finite-leavitt-representations-killing-defect-are-trivial` (also graph);
  - `ternary-weakly-finite-representations-give-anti-central-images`;
  - `weakly-finite-reflection-ideal-detects-weakly-finite-images`;
  - flattening of the triangular certificates.
- **Spectral and state results** (gk-vf-linear-b):
  - §9: `hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent`;
  - §12 and §15: anti-central K_0 states;
  - §24: `anti-central-state-exists-iff-lifted-trace-relatively-positive`;
  - §30: the RGR_p cyclic reduction.
- **Blocks and charts** (w6-wf-stage1-a and -b): semidihedral and `GL_2(F_3)` blocks, the two-piece corner criterion,
  and the finite-dimensional chart filter. gk-vf-linear-b §40, §41.
- **Two-root identity and scope** (gk-vf-linear):
  - §47: the two-root identity is corner-local;
  - §56: corner rank data, parts 1–3 (the level route is a restatement);
  - §57: characteristic 3 scope.
- **The V law in characteristic 3.** [CG] Theorem 1.1 is verified at w3-vf-linear §33.4. §33.3 corrects the scope: "the
  law needs a prime other than 3" is proved only for elementary abelian data.

**Paper.**
- **w7-matrix-state-deficit** (f3545c8591). The ternary strict deficit restates emptiness in both scopes. It covers:
  - `ternary-anti-central-matrix-state-defects-have-a-strict-deficit` (OPEN);
  - `ternary-anti-central-disjoint-defects-have-a-strict-deficit` (OPEN);
  - `rank-condition-rings-have-weakly-finite-images` (graph).
- **w7-escape-set** (45282c2142). Verifier PASS: gk-vf-gate §36 on Sections 1–4, with no correction. The claim
  `four-transvections-and-x23-force-defect-vanishing` stays OPEN.
  - The four-transvection set `S4` escapes the depth-monotone units: `four-transvection-set-escapes-depth-monotone-units`.
  - `<S4>` has a weakly finite symbol image with `z -> -1`: `four-transvection-units-have-a-weakly-finite-symbol-image`.
    So form (iii) is firewalled.
  - Depth-monotone units carry a weakly finite representation with nonzero defect:
    `depth-monotone-units-carry-weakly-finite-nonzero-defect`. So form (iv) is firewalled on depth-monotone
    configurations.
- **w7-yh-rank-firewall** (b54cf150e8, verification by w4-vf-linear-b requested by the lane):
  `one-transvection-s0-lift-has-no-left-inverse`.
  - Let `d` be an involution outside `<z>`. If `P_d[h]P_d` has a left inverse in `P_d S_- P_d`, it is invertible.
  - The reason is that a left inverse projects onto `k[W]` with `W = <z, d, h^-1 d h>` virtually cyclic.
  - Once verified, it refutes `one-transvection-ternary-s0-lift-is-left-invertible` and invalidates the route
    `one-transvection-s0-lift-refutes-ternary-surjunctivity`.
- **w7-v-gate-c3** (f5b2406faa), at `<x_0, x_1, s>`:
  - rank models break on mixed-prime finite groups;
  - generation fails for natural `s`;
  - Proposition 5.2 needs an extension.

  Verifier PASS: w3-vf-linear §34 and §34.7, partial, with the [CFP] and [VX] inputs taken as cited. Nothing is decided.
- **w7-v-rank-split** (3756340b80), `v-rank-functions-split-as-augmentation-plus-reduced`:
  - Over every field, if `phi_V < 1` then `rk_0 = (rk - phi_V rk_aug)/(1 - phi_V)` is a Sylvester matrix rank function
    with `phi_V(rk_0) = 0`.
  - The rank functions on `F[V]` form the join of `rk_aug` and the face `P_0 = {phi_V = 0}`.
  - `<x_0, x_1, t>` contains `V_O ≅ V`, so it is sofic iff V is.

**Dead.**
- **Verbatim transfer of the binary methods.** Over `F_3`, `1 + s0 t1` has order 3.
- **Depth-monotone data as the source of defect vanishing.**
  - `depth-monotone-leavitt-subalgebras-are-stably-finite`: gk-vf-gate §30.
  - The nonzero-defect model of 45282c2142 (gk-vf-gate §36).
- **Two-piece lifts of `s0` over the involution partition of `d1`.** Dead once b54cf150e8 is verified.

**Where it stops.**
- The open lift is `ternary-leavitt-swap-idempotent-is-full` (OPEN). It holds in the Leavitt algebra itself.
- Its emptiness form is `ternary-leavitt-units-have-no-weakly-finite-representation` (OPEN), through
  `ternary-weakly-finite-representations-kill-two-root-defect` (OPEN).
- The load sits on one closing letter: `four-transvections-and-x23-force-defect-vanishing` (OPEN), with
  `Gamma_5 = <S4, x_23(1)>`.
- Chain C1 closes this root through two lemmas:
  - (K) `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`;
  - (U1b) `anti-central-weakly-finite-images-carry-rank-functions`, which is Hung–Li Question 3.4, reached through
    `rank-condition-rings-carry-sylvester-rank-functions`.

  Both are OPEN.

### 1.3 `projective-ternary-leavitt-group-nonsurjunctive` (`PG = G / F_3^x`)

- **Host.** `PG` is nonsofic: `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`.
- **Reduction.** Reduced to `projective-ternary-swap-idempotent-is-full` (OPEN). That is implied by
  `ternary-leavitt-swap-idempotent-is-full`.
- **The anti-central half suffices.** This is `ternary-anti-invariant-swap-corner-is-full` (OPEN, C3), with the
  correction by gk-verify-pos recorded on the root. The Leavitt image equation already holds on that half.
- **Where it stops.** It is the same lift as 1.2, on the anti-central summand. Simplicity of `PG` is also the input
  that makes the ternary chain an equivalence.

### 1.4 `some-finite-field-leavitt-unit-group-nonsurjunctive`

- **Reduction.** The route `cyclic-corner-fullness-refutes-leavitt-host-surjunctivity` reduces it to
  `leavitt-visible-cyclic-corner-is-full-on-some-host` (OPEN). The image equation holds in the Leavitt algebra on every
  host.
- **Implied by the special cases.** Both the binary and the ternary root imply it:
  `binary-nonsurjunctivity-gives-finite-field-leavitt-host` and `ternary-nonsurjunctivity-gives-finite-field-leavitt-host`.
- **Where it stops.** This is the weakest Leavitt root, and still no host has a lifted corner. Every host is nonsofic.

### 1.5 `brin-thompson-2v-nonsurjunctive`

- **Ascent.** The route `thompson-v-nonsurjunctivity-ascends-to-brin-thompson-2v` (`V <= 2V`).
- **Checked** (w3-vf-nonlinear §29 and §31):
  - The Theorem B transfer to `F_2[2V]`, the baker unit and product tower, and the reduction of `H_u = <V ⊗ 1, u>` to V
    (w6-free-neg-d).
  - The obstruction-state profile (w7-2v-mixed-support: afb6eb112e, 77aed2b4fd, 9a375e7cd9). §31 finds Section 2
    correct, and both claim nodes stay OPEN.
- **Value gap.** Every state of `K_0(F_2[2V])` gives `b <= 2/9`, and the augmentation gives `b = 0`. If some state gives
  `b > 0`, then some state gives `b = 2/9`.
- **Where it stops.** The target `brin-thompson-2v-order-three-averaging-idempotent-is-full` (OPEN). Three options are
  undecided:
  - 2V fullness ⟺ V fullness;
  - mixed-support relations over `H_mix = <V ⊗ 1, 1 ⊗ h, u>` that kill `b = 0` and `b = 2/9`;
  - an obstruction state.

### 1.6 `higman-group-nonsurjunctive`

**Verified.**
- w3-vf-nonlinear §23: `higman-group-splits-as-amalgams-over-free-subgroups` and the edge-group filter. Both claims
  PASS.
- w3-vf-nonlinear §25: `higman-group-is-the-swap-twisted-double-of-a-bs-amalgam`.

Both nodes are also ESTABLISHED in the graph.

**Host facts.** Higman's group is finitely presented, torsion-free and perfect, has no finite quotients, and has only
trivial finite-dimensional representations. So finite and linear covers see nothing.

**Artifact** (`research/artifacts/higman-group-gottschalk-host-2026-09-12.md`):
- copying maps on each piece are exactly two-to-one;
- the group has girth five in its standard generators.

**Dead.** Linear automata over one track are dead: unique products block them (artifact Section 3).

**Where it stops.** No candidate design reads all four pieces through the free edge groups.

### 1.7 `kun-thom-wreath-lamp-quotient-nonsurjunctive`

**Verified.**
- w3-vf-nonlinear §17: `kun-thom-lamp-quotients-have-lamp-sofic-radical`.
- gk-vf-nonlinear §22: Rokhlin maximality under local embeddings, and the Kun–Thom wreath witnesses.

**Graph.**
- `residually-permutational-lamp-extensions-are-surjunctive`: closed submodules are dead.
- `strict-lamp-quotient-realizations-need-lamp-hinges`: the decoder must read `U`.

**Artifact facts.**
- Finitely many lamps suffice.
- Finite coset spaces are blind, because `Gamma` is profinitely dense in `N`.
- The smallest test is decided negatively for free generators.

**Dead.** The coset-parity closure equivalence for the commutator generator is FALSE as stated (w3-vf-nonlinear §21).

**Where it stops.** No non-closed submodule of `K_even` has been exhibited, and no design is known.

### 1.8 `deligne-triple-cover-nonsurjunctive`

**Verified.**
- w3-vf-positive §7: finite normal p-subgroups, all three claims. Nothing there decides surjunctivity.
- gk-vf-linear-b §22 (w4-deligne-twisted): Lemma 1.1 and Proposition 3.1 PASS; Theorem 2.1 is pending.
- gk-vf-linear-b §25: rank rigidity (w4-deligne-projective).

**Dead.**
- In characteristic 3, linear witnesses are dead: the cover is not linear and not formalizable over `F_3^n`.
- Its memory group contains the central `z`, with `z` in the finite residual, and is nonsofic.

**Where it stops.**
- For `p != 3` the target is `deligne-twisted-group-algebra-is-not-stably-finite` (OPEN).
- No known mechanism uses a non-inflated multiplier to produce a one-sided pair.

### 1.9 `kun-thom-clifford-cover-nonsurjunctive`

**Verified.**
- w3-vf-nonlinear:
  - §3: `kun-thom-clifford-cover-has-no-finitary-site-structure`, so permanence cannot reach this host;
  - §7: `clifford-cover-center-separable-iff-graph-is-finite-pullback`;
  - §11: `clifford-cover-strict-pairs-read-invisible-adjacency`;
  - §18: `phase-windows-have-no-separated-clifford-realization`;
  - §22: copying-rule lifts and self-dual flux sectors.
- gk-vf-linear-b:
  - §6: the refutation-chain route;
  - §14: `oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath`;
  - §16;
  - §19: `infinite-clique-clifford-algebras-have-no-bounded-spin-models`.

**Claims on the root.**
- `complete-graph-clifford-cover-center-dies-in-finite-quotients`.
- `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring` reduces the linear case to direct finiteness of the
  anti-half skew ring.

**Dead.** The binary linear case, by the p-subgroup argument.

**Where it stops.**
- Linear: `clifford-cover-anti-half-skew-ring-not-directly-finite` (OPEN).
- Nonlinear: orbital localization yields no design.

### 1.10 `strict-automaton-on-lattice-in-product-of-trees`

**Verified.**
- gk-vf-nonlinear §28: VH lattice hosts, with the host filter `vh-lattices-surjunctive-when-a-factor-maps-faithfully`
  (also graph).
- w3-vf-nonlinear §5: `strict-composites-have-strict-factors`.
- gk-vf-linear-b §26: Radu's BMW lattice (w4-radu-f2; 9455d4a271, 85b6407404, eb6760902f).

**Graph.** `radu-lattice-one-sided-pairs-need-radius-five` (c7fbc72300). Its input is Remark 3.6 of Titz Mite–Witzel,
arXiv:2509.05054v2, which is a computer check.
- **Theorem A.** Supports of total radius at most 4 carry no one-sided pair over any field, at any size.
- **Theorem C.** Under hypothesis H10, total radius 5 carries no pair either.

**Paper.** `radu-lattice-radius-two-pairs-force-the-mark-into-the-radical` (86e9c2b3e8).

**Dead.**
- square-read shift–shear designs;
- star and mixed-bigon partitions;
- the support pairs `(B_2,B_2)`, `(B_1,B_3)` and `(B_3,B_1)`.

**Where it stops.**
- The open targets are `radu-bmw-lattice-nonsurjunctive` and `radu-bmw-lattice-group-algebra-not-stably-finite`.
- Linear pairs need total radius at least 5, and at least 6 under H10. Lemma B stops at radius 6, because `C_6`
  contains `delta` and `delta^2`.

## 2. The R4 gate family: route `leavitt-el3-triviality-via-rank-four-cuntz-family`

**Verified inputs** (gk-vf-gate):
- **Corners and defects.**
  - §2: `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple`;
  - §4: `toeplitz-isometry-defects-have-total-rank-at-least-one`;
  - §6: `index-three-corner-placement-holds-only-modulo-two-root-defects`;
  - §7: `leavitt-completeness-transport-formula-for-root-data`;
  - §9: `opposite-unit-root-product-vanishes-only-for-trivial-models`.
- **Gap and descent.** §8: `leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`.
- **Cylinder commutants.**
  - §11: `near-minimal-defects-are-rank-independent-of-cylinder-commutants`;
  - §13: `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant`;
  - §19: `disjoint-root-halves-row-plus-column-rank-at-most-three-rho`.
- **The gate as emptiness.** §14: `two-root-identity-in-all-models-iff-no-nontrivial-model`.
- **Matrix-state bounds.** gk-vf-linear-b §42 (lane w6-upg-separate, fdf1237ec2) PASSES two things: lower bounds for
  the two-root gate, and commuting Jordan certificates for matrix states.
- **Compressions.**
  - §17: `thompson-v-lifts-into-rank-four-cohn-elementary-group`;
  - §18: `regular-rank-ring-compressors-conserve-fixed-right-ideals`;
  - §21: `signed-thompson-z-moving-rank-functions-match-v-rank-functions`;
  - §23: `sylvester-rank-functions-compress-along-commuting-elements`;
  - §24: `cohn-pair-compression-embeds-el-2n-into-el-n`;
  - §26: `sylvester-rank-functions-descend-to-quotients-and-compressions`.

**Dead.**
- **R4 as a reduction.**
  - The strict deficit `theta < 1` is the gate restated. In characteristic 3 this is f3545c8591 (paper). In
    characteristic 2 it is w7-sylv-global §4.2, inside gk-vf-linear-b §39.
  - By §14 the gate is the emptiness of nontrivial rank models.
  - So R4 closes only through a certificate for emptiness: a one-sided pair `XY = I_n` over `S_-`, or a proof that no
    Sylvester rank function exists.
- **Plan 1.** `unipotent-frame-relations-cannot-assemble-corner-cuntz-family` (c6697aa47b), §3.
- **Heisenberg data.** `unitriangular-data-cannot-assemble-corner-leavitt-families` (f576dccf26), §5.
- **Halving.** Halving is locally finite data (f25ccc5958), §10.
- **The K_2(3,R) option.**
  - `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` (8afa079662), §34.
  - The Steinberg firewall has no K_2 escape at rank three for the binary and ternary hosts.
- **Averaging and Hamming extensions.**
  - w6-v-extend, §33 (verifier commit 5b4dce2717). Neither averaging nor a Hamming extension extends the V-detecting
    rank functions.
  - The first reduction link is equivalent to the V gate.
  - `v-detecting-rank-functions-extend-to-ternary-leavitt-units` stays OPEN.
- **L3 as a step.** `cohn-coefficient-el3-rank-models-satisfy-two-root-identity` (OPEN) is, by §14, the emptiness of
  nontrivial models of that kind. It is not an easier step.

## 3. Firewalls and what each rules out

Section numbers are gk-vf-gate unless another verifier is named.

| firewall | node and verification | rules out |
|---|---|---|
| finite subgroups | `finite-subgroup-data-cannot-force-defect-submultiplicativity` §16.1; Toeplitz pair §28.1 | forcing strict submultiplicativity from finite-subgroup relations, the Toeplitz pair included |
| locally finite HNN | `locally-finite-hnn-data-allow-independent-cylinder-defects` §15.1; `binary-locally-finite-hnn-models-violate-two-root-identity` §20.1 | forcing the two-root identity from locally finite HNN data |
| monotone families | `covariant-monotone-cylinder-families-in-rank-models-are-constant` §12.1 | separating rank values by covariant monotone cylinder families |
| anti-central sofic data | `anti-central-sofic-data-cannot-force-defect-submultiplicativity` §22.1 | sofic subgroup data on the anti-central half |
| commuting witnesses | `commuting-subgroup-witnesses-cannot-distort-defect-ranges` §25.1 | distorting defect ranges through commuting subgroups |
| graphs of groups | `graphs-of-locally-finite-groups-carry-regular-rank-models` §29.1 | relations inside graphs of locally finite groups |
| depth-monotone | `depth-monotone-leavitt-subalgebras-are-stably-finite` §30.1 | one-sided pairs on depth-monotone subalgebras |
| multi-letter three | `split-cylinder-data-cannot-force-defect-submultiplicativity`, `lex-decreasing-units-with-order-preserving-letters-are-amenable` §35 (lane w7-sub-multiletter) | lexicographic Borel letters, cylinder swaps, one-chart coefficients. Lemma 6.1 needs the roots of each frame to move in one common direction (§35.4); the correction is applied in §37 |
| Jacobson EL_3 | `jacobson-elementary-subgroups-are-locally-finite-by-linear`, `jacobson-elementary-groups-are-lea-only-if-lef` §31; `jacobson-one-sided-symbol-preimages-are-lef` §32 | V, `R^x` or `EL_3(C_2)` inside `EL_3(J)`, and the one-sided halves, as nonsoficity sources |
| V cylinder law | w3-vf-linear §32 | rank values on finite subgroups of V other than trivial plus regular |
| p-cycle tree | `p-cycle-tree-invariance-cannot-force-order-char-law`, w3-vf-linear §33, scoped to elementary abelian groups | proving the order-char law from endomorphism-invariant p-cycle tree models |
| averaging, Hamming | §33 | extending V-detecting rank functions by averaging or Hamming transport |
| Steinberg K_2 | §34 | unstable K_2 at rank three as an escape |
| unipotent frames | §3, §5 | a corner Cuntz or Leavitt family from unipotent or unitriangular data |
| Kazhdan rounding | `kazhdan-group-rank-models-admit-no-expander-decomposition` (graph) | rank rounding from property (T) |
| escape-set symbol | gk-vf-gate §36 (45282c2142) | form (iii) through `<S4>`; form (iv) on depth-monotone configurations |
| dihedral support | b54cf150e8 (paper) | two-piece lifts of `s0` over an involution partition |
| chain converse | gk-vf-chain §4 | reading a failed linear route as a no-go for counterexamples |
| permanence closure | `gottschalk-counterexamples-lie-outside-the-permanence-closure` (graph) | positive proofs by the available permanence theorems |
| table realization | `strict-pairs-transfer-to-table-realizations` (graph) | certificates whose orphan cells survive a map into a finite or surjunctive group |
| algebraic subshifts | `full-shift-maps-into-two-sided-algebraic-subshifts-are-constant` (graph) | constructions through the dual of the Leavitt algebra |
| host filters | `vh-lattices-surjunctive-when-a-factor-maps-faithfully`; `residually-permutational-lamp-extensions-are-surjunctive`; `kun-thom-clifford-cover-has-no-finitary-site-structure`; Higman edge groups (w3-vf-nonlinear §23) | lattices with a faithful factor; closed lamp submodules; permanence on the Clifford cover; designs that read Higman's pieces through edge groups alone |
| formalizability | gk-vf-nonlinear §23, §24, §27, §29 | formalizable designs; binary formalizability is false |

The team rules also record design filters as settled: nonsofic forward core, triangular tables, holonomy normal form,
amenable decoder memory, independent cycles, measure distortion, and one decidable host (Π⁰₂).

**The common pattern.** One-sided or ordered data are approximable by rank models. The load sits on closing or
order-breaking letters:
- the Toeplitz commutators;
- `t` in `Y_hex`;
- `b` in `Gamma_b`;
- `x_23(1)` in `Gamma_5`.

## 4. Ranked next leads

1. **The one next lead: `four-transvections-and-x23-force-defect-vanishing`**, at `Gamma_5 = <S4, x_23(1)>` on the
   ternary host.
   - Every weaker configuration is firewalled: depth-monotone data, the symbol image, finite subgroups, HNN data and
     multi-letter data. The load sits on `x_23(1)` alone.
   - Success feeds `ternary-weakly-finite-representations-kill-two-root-defect`, then
     `ternary-leavitt-units-have-no-weakly-finite-representation`, then Rep_3, then
     `ternary-leavitt-unit-group-nonsurjunctive`, which refutes the goal.
   - The inputs are verified: gk-vf-gate §36 PASSES 45282c2142, and shows that
     `summand-obstruction-from-four-transvection-defect` is a valid implication.
   - Still OPEN:
     - soficity of `<S4>` and of `Gamma_5`; soficity of `Gamma_5` would refute the claim;
     - whether `<S6> = G`;
     - conjugate frames inside `<S4>`.
2. **Chain C1.** `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` (K) together with
   `anti-central-weakly-finite-images-carry-rank-functions` (U1b, Hung–Li Question 3.4, through
   `rank-condition-rings-carry-sylvester-rank-functions`). This is the emptiness certificate through rank functions.
3. **The ternary V gate.** `thompson-v-ternary-rank-functions-are-augmentation`, with
   `v-rank-functions-split-as-augmentation-plus-reduced`. Decide whether the face `{phi_V = 0}` is empty over `F_3[V]`.
   By §33 the first reduction link is equivalent to this gate.
   - w3-vf-linear §34 PASSES the joint configuration at `<x_0, x_1, s>` (f5b2406faa): which relation breaks the
     models, generation, and what a `phi_V < 1` model would do. This is a record and a firewall, not the gate itself.
   - The split 3756340b80 still needs a verifier.
4. **`binary-jacobson-el3-is-sofic`**, with `binary-jacobson-el3-is-finitely-presented`. On paper (8fc212cf45) the
   amalgam kernel is residually finite. A sofic answer firewalls the closing letters of the R4 family; a nonsofic one
   localizes the gate.
5. **`ternary-anti-invariant-swap-corner-is-full`** (C3), and so `projective-ternary-swap-idempotent-is-full`. A lift
   must leave the dihedral support of b54cf150e8.
6. **`brin-thompson-2v-order-three-averaging-idempotent-is-full`.** Decide `b` in `{0, 2/9}` over `H_mix`.
7. **`radu-bmw-lattice-group-algebra-not-stably-finite`.** Search supports of total radius at least 6, or prove H10.
8. **Host lemmas (C5).** `clifford-cover-anti-half-skew-ring-not-directly-finite` and
   `deligne-twisted-group-algebra-is-not-stably-finite` (`p != 3`).
9. **Binary chain C2.** `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`, or `thompson-v-nonsurjunctive`.
10. **Positive side.** `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` with
    `zero-rokhlin-supremum-forces-bernoulli-collapse`.

## 5. Verification queue at wrap-up

These landings are held OPEN. The "natural verifier" is the family verifier for each one.

| landing | lane or topic | content | natural verifier |
|---|---|---|---|
| f3545c8591 | w7-matrix-state-deficit | the strict deficit restates emptiness | w4-vf-linear-b |
| 8fc212cf45 | w7-el3j-presentation | amalgam kernel, presentation reductions | w4-vf-gate |
| b54cf150e8 | w7-yh-rank-firewall | `one-transvection-s0-lift-has-no-left-inverse` | w4-vf-linear-b |
| 3756340b80 | w7-v-rank-split | splitting off the augmentation rank | w3-vf-linear |
| 86e9c2b3e8 | Radu, radius two | mark forced into the sofic radical | w3-vf-nonlinear |
| c7fbc72300 | Radu, radius five | ESTABLISHED in the graph, no verifier section traced | w3-vf-nonlinear |
| 286ccdcb36, 9c34e9e7f5 | Rokhlin dichotomy | zero-or-full collapse; the bridge claim | gk-vf-positive-b |
| 14a3ca5645, 0f2758222e | ex-free-objects | presentations of `L_(F_2)(1,2)^x` | unreviewed |
