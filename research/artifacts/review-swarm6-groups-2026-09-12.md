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
- **Swarm-4 §39.1–39.2** (c0ffe2f06, 20:54) recorded PASS on eight claims this lane was reading, including §1–§3
  here.
  - This lane's verdicts on §1–§3 stand, and two of them differ from §39. §2 finds
    `free-splitting-fa-lifts-choose-a-side` false as stated, where §39.2 has PASS. §3 adds the degenerate case `N = 1`.
  - The other five are skipped here. This lane's reads also give PASS, and add the following points.
  - **`osin-isolated-components-bounded-by-relative-area`.**
    - Osin's `math/0404040` was fetched on MSI (20:49), and Definitions 2.24–2.25 and Lemma 2.27 were re-read.
    - Lemma 2.27 assumes a reduced finite relative presentation. Def. 2.24 says every relative presentation may be
      assumed reduced, and Def. 2.25 says `Ω` is finite when `R` is finite.
    - The node's item 1 is Def. 2.25. Item 2 is (2.7)–(2.8) with `M = max_{R ∈ R} ‖R‖`, followed by the linear
      relative Dehn function.
  - **`fpbs-surface-group-times-zk-product-sets-strict-thresholds`.** The statement is correct, but the title
    overclaimed.
    - The title said "times `Z^k`" with no restriction on `k`. The statement needs
      `2k < 1 + √((4g−2)² − 4) − 4√g`, and for example `Γ_3 × Z²` fails that bound (`4 > 3.87`).
    - The listed range `k ≤ max(1, g−2)` is sufficient, not sharp: `g = 4` also allows `k = 3`.
    - The title now names the range.
  - **`fpbs-expanding-factor-product-strict-thresholds`, `fpbs-generating-set-threshold-comparison` and
    `fpbs-generating-sets-connected-by-product-moves`.** No further points.

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

**Correction (091dcc952).** The node's Setting now requires `Λ` to have finite index in `J_B` and records the
two examples above. Step 4 of the route now gives the star argument.
`cairn why` at 3d4faea64 on MSI still gives ESTABLISHED through the direct proof.
The node's title on main (687fe4da3) still says "over an FA factor-automorphism subgroup". An edit in the shared tree
(21:15, not this lane's) adds "finite-index", and this lane has not landed it.

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
  - The node's Setting now says so (091dcc952).
  - `fpbs-line-independent-twisted-levels-disconnected` (swarm 7) takes its `δ_0` from this node, so it inherits
    the restriction.
- **Imports.**
  - For Osin's Lemma 2.27 see §0.
  - `hyperbolic-group-relative-to-maximal-elementary-subgroup` was not re-read.

## 4. `el3-of-infinite-rank-rings-not-linear-over-number-fields` (2bc488e31): PASS

Suslin's theorem appears only in the Examples and was not re-read.
- **Finite generation.** For `n ≥ 3`, `EL_n(R)` is generated by the `E_ij(r)` with `r` among `1` and the ring
  generators, since `[E_ik(a), E_kj(b)] = E_ij(ab)`. So `Λ` is finitely generated, and "linear over `Q̄`" is the
  same as "linear over a number field".
- **Distortion.**
  - Put `d = [EL_n(R) : Λ]` and `q = d!`. By pigeonhole on cosets, `E_ij(x)^q ∈ Λ` for every `x`.
  - With `g_a = E_12(q² a)`, `g_a^{m²} = [E_13(qa)^m, E_32(q)^m]`, so `|g_a^k|_Λ ≤ C_a √k`.
  - Nothing here uses commutativity of `R`.
- **Eigenvalues.**
  - Let `ρ : Λ → GL_N(K)` be faithful. At each place `v`, `‖ρ(g_a)^k‖_v ≤ M_v^{C_a √k}`, so every eigenvalue has
    absolute value at most 1. The same bound for `g_a^{-1}` gives at least 1.
  - So the eigenvalues are algebraic integers whose conjugates all lie on the unit circle, and Kronecker makes them
    roots of unity.
  - Their degree is at most `N[K:Q]`, so their orders divide a fixed `e`, and `ρ(g_a)^e` is unipotent.
- **Rank.**
  - The map `a ↦ log ρ(E_12(e q² a))` is additive, because the `E_12(x)` commute and `log` is additive on commuting
    unipotents.
  - Faithfulness makes its kernel torsion. So `(R, +)` has torsion-free rank at most `N²[K:Q]`, which contradicts
    `dim_Q R ⊗ Q = ∞`.
- **Hidden hypotheses.** None found.

## 5. `el3-z-t-embeds-in-no-host-with-number-field-local-groups` (2bc488e31): PASS, conditional on imports reviewed elsewhere

The imports have their own verdicts: `fw-subgroups-of-eventually-similar-groups-virtually-embed` in `review-swarm4`,
and `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` in `review-swarm4` and `review-backlog-2`.
- **Route.**
  - (T) passes to finite-index subgroups, and (T) implies (FH), which implies FW.
  - Either theorem puts a finite-index `Λ_0` inside a finite product of vertex groups, or inside `H^m`.
  - Block-diagonal placement makes that product linear over `Q̄`.
  - `Λ_0` has finite index in `EL_n(R)`, so §4 applies.
- **Trivial groupoid.** Part 2 of the transfixing theorem makes `Λ` finite. But `Λ ∩ E_12(R)` has finite index in
  `(R, +)`, which is infinite.
- **SFT full groups.** An element given by pairs `(u_j, v_j)` maps `C_u` onto `C_{v_j u'}` whenever `u = u_j u'`,
  by a canonical similarity. So it is eventually similar with trivial `H`.
- **Scope.** The listed host families claim nothing beyond items 1–2.
  - Zaremsky's affine groups over a ring inside a number field are linear over that field.
  - That they are self-similar is Zaremsky's result, and it was not re-read.

## 6. `elementary-groups-over-fg-rings-have-property-t` (2bc488e31): PASS as a citation, source re-read

- **Source.**
  - This lane fetched the arXiv e-print `0809.4095v2` with curl on MSI at 21:02, into
    `/scratch.global/sauer354/rv6g/ejz/`.
  - In `EL_n0909.tex`, lines 405–410 hold `\label{thm:main}` and the quoted statement word for word.
- **Nit, corrected forward.** The citation route put the file in `/scratch.global/sauer354/fcah/`, but it is in
  `fcah/src/`. The route now gives the full path.
- **Consequences.**
  - (T) passes to finite-index subgroups, and (T) implies (FH), then FW, then FA.
  - Suslin's `SL_3(Z[t]) = EL_3(Z[t])` was not re-read.

## 7. KL substitution and residue sub-cases (bfa2e6677, 16:21): three PASS, conditional on imports

These landed shortly before 17:00, and no review file has a verdict on them. Two imports were not re-read.
- `kl-length-at-most-five-equations-are-solvable` (Howie; Edjvet–Howie; Evangelidou). Its citation route states
  its own trust surface.
- `kervaire-laudenbach-holds-for-hyperlinear` (Nitsche–Thom, Theorem 1.2).

### 7.1 `kl-substituting-a-short-inner-word-preserves-injectivity`: PASS

- **Inner equation.** `u(t) z^{-1}` over `H` has variable length `ℓ_t(u) ≤ 5` and degree `deg_t(u) ≠ 0`.
  Cyclic reduction only shortens it, so `H → P` is injective.
  - The coefficient group `H` is arbitrary, and the length-five import allows that.
- **Pushing `w` through.** `φ ∘ σ_u` and `ψ` agree on `G` and on `z`, so `φ(w) = ψ(v) = 1`.
- **Injectivity.** The composite `G → (G ∗ ⟨t⟩)/⟨⟨w⟩⟩ → P` equals `G → H → P`, which is injective.
- **Degree formula.** It follows by composing `σ_u` with the degree map.
- **Unused hypotheses.** The proof uses nothing about torsion or cancellation.

### 7.2 `kl-length-six-residue-squares-and-fourth-powers-inject`: PASS

- **Identities.**
  - (S1)–(S4) were multiplied out by hand, and (S3)–(S4) checked by the stated induction.
  - (S2) and (S4) hold after conjugating by `t^{-1}x`.
- **Outer equations.** `z^k c` with `k ∈ {2, 4}` injects `G`, through the amalgam along `z^k = c^{-1}`.
- **Substitution.** The inner word `u` has length 4 and degree 2, or length 3 and degree 1, so 7.1 applies.
- **Normalizing shift.** `t ↦ s c^{-1}` sends `a_i ↦ c^{-1} a_i` and `y ↦ c^{-1} y c`, fixes `x`, and preserves each
  of (S1)–(S4).
- **Table.** All 32 cells were rechecked against the eight `+++++-` shapes of
  `kl-length-six-coincidence-saturated-torsion-residue`.
  - The hits are `(1,1,g,1)` with `g = y`, `(g,1,1,1)` with `g = y^{-1}`, `(1,g,1,1)` with `g = x`, and
    `(1,1,1,g)` with `g = x^{-1}`.
  - Loop coefficients of cyclically reduced words are nontrivial, so the cells needing `x = 1` or `y = 1` never
    apply.

### 7.3 `kl-two-coefficient-residue-word-with-involution-loops-injects`: PASS

- **Setting.** The coefficients of `t^5 y t^{-1} x` are `x` and `y`, and its degree is 4.
- **Localization.** It is the pushout `G_w = G ∗_A A_w`.
- **Involutions.** If `x² = y² = 1`, then `⟨x, y⟩` is a quotient of `D_∞`. So it is amenable, hence sofic, hence
  hyperlinear.
- **Unnormalized words.** The automorphism `t ↦ s u^{-1}` gives `s^5 (u^{-1} y u) s^{-1} x`, as stated.
- **Loop orders 2 and 3.** That paragraph claims nothing.

## 8. Minimal aperiodic `Z²` SFTs and their full groups (0152a082a, 17:46): four PASS

### 8.1 `minimal-aperiodic-wang-shift-exists`: PASS as a citation, source re-read

- **Source.** In `/scratch.global/sauer354/fpsz2/src/1802.03265.d/article1.tex`, lines 295–298 hold
  `\label{thm:main}`: "The Wang shift `Ω_U` is self-similar, aperiodic and minimal."
- **Consequences.**
  - Wang shifts are nearest-neighbour SFTs by definition.
  - "No nontrivial period" is freeness.
  - An infinite minimal subshift has no isolated point, so `Ω_U` is a Cantor set.

### 8.2 `minimal-z2-subshift-derived-full-groups-are-fg-simple`: PASS as a citation, sources re-read

- **ChJN, `1602.04255.d/IET_copy.tex`.**
  - Lines 81–85, Theorem `main`: for a minimal faithful `Z^d`-action conjugate to a subshift, `[[Z^d]]'` is finitely
    generated. A free action is faithful.
  - Line 86: `A(G)` and the derived subgroup coincide for actions of abelian groups.
  - Line 207 quotes Matui: `[[Z^d]]'` is simple and lies in every nontrivial normal subgroup.
  - Line 209: the order-3 cycles of clopen sets generate `[[Z^d]]'`.
- **Nekrashevych, `1511.08241.d/fullgr.tex`.** Lines 117–125 give simplicity of `A(G)` for minimal groupoids of
  germs, and finite generation in the expansive case.
- **Infinite.** A free action on a perfect space has 3-cycles supported on arbitrarily small clopen sets.

### 8.3 `sfts-without-finite-orbits-are-not-residually-finite-actions`: PASS

- **Assembly.** For `s ∈ K`, `ε_0`-closeness gives `y(sλ) = (β(λ) z_0)(s)`. So the `K`-pattern of `y` at `λ` is that
  of a point of `X`, and `y ∈ Y`.
- **Finite orbit.** `y(λl) = y(λ)` for every `l` in the finite-index `Stab_β(z_0)`.
- **Hidden hypotheses.** If the finite model is given by a map `ζ : E → X` rather than a subset `E ⊆ X`, put
  `y(λ) = ζ(β(λ) z_0)(e)`. The same argument then works.
- **(PA).** The definition in `periodic-approximable-subshifts-host-no-fp-simple-group`, applied with `K` the SFT shape,
  yields a finite-orbit point of `Y` directly.
- **Source not re-read.** Ma's Definition `defn: residually finite action` (arXiv:2209.00580).

### 8.4 `labbe-shift-derived-full-group-escapes-known-obstructions`: PASS

- **Item 1** follows from 8.1 and 8.2.
- **Item 2.**
  - Compact open bisections of `Z² ⋉ X` are finite unions of translated clopen sets, so they preserve an invariant `μ`.
  - Then `μ(A) ≥ 2μ(A)` forces `μ(A) = 0`, which contradicts full support.
  - So the Corollary (item 3) of `amenable-full-group-forces-invariant-measure` does not apply.
- **Item 3.** `X` is itself an SFT. So `Y = X` and `ĝ_i = g_i` satisfy item 1 of
  `fp-subshift-full-group-subgroups-extend-to-sft`, and its item 2 says nothing.
- **Item 4** is 8.3 with `X = Y = Ω_U`.
- **Open parts.** Amenability and finite presentation are correctly OPEN and were not reviewed here.

## 9. `minimal-free-sft-full-group-pattern-models-are-exact` (6a387929b): PASS

- **Hypotheses.** A validly coloured `Z^d`-set is nonempty by definition (claim line 21). `X` is free, minimal and
  exactly the SFT on `K`. So every `x_ω` lies in `X`, and `f_s(x_ω)` is defined.
- **Display check, route Steps 1–7.**
  - `x_{λ·ω}(μ) = c(μ·λ·ω) = (λ·x_ω)(μ)`.
  - Freeness: `λ·ω = ω` gives `λ·x_ω = x_ω`, so `λ = 0`.
  - Cocycle: `gh(x) = f_g(hx)·f_h(x)·x`. Freeness of `X` makes `f_{gh}(x) = f_g(hx) + f_h(x)` the only solution.
  - Homomorphism: `g_Ω(h_Ω ω) = f_g(f_h(πω)·πω)·f_h(πω)·ω = f_{gh}(πω)·ω`.
  - Injectivity: if `g_Ω = id`, freeness of `Ω` gives `f_g = 0` on `π(Ω)`. That set is nonempty and invariant, hence
    dense, and `f_g^{-1}(0)` is clopen. So `f_g ≡ 0` and `g = 1`.
- **Every model gives the same marked group.** Nothing above uses `(Ω, c)` beyond validity and nonemptiness. So every
  validly coloured `Z^d`-set gives `(Γ, S)`.
- **Isolation lemma** (claim line 32, route lines 45–51).
  - Isolated ⇒ f.p.: the kernels of `Γ_n` increase to the kernel of `Γ`, so `Γ_n → Γ`. This needs only finite
    generation.
  - F.p. ⇒ isolated: "all of `R` vanish and `s_0 ≠ 1`" is a finite intersection of clopen conditions. A marked group
    in it is a quotient of `Γ` whose kernel misses `s_0`. Simplicity makes that kernel trivial. This needs simplicity
    and `s_0 ≠ 1`, nothing more.
  - "Infinite" is never used. Finite simple groups are also f.p. and isolated. So the extra hypothesis is harmless, and
    none is missing.
  - The node proves the lemma itself and cites no source. Cornulier–Guyot–Pitsch: source not re-read.
- **Consequence** (route lines 55–59). `Z ≠ Ω_U` gives `Z ⊄ Ω_U`, because a nonempty closed invariant subset of the
  minimal `Ω_U` is all of it. Minimality of `Z` then makes the defects syndetic. Nothing is claimed about finite
  presentation.
- **OPEN node.** `labbe-shift-derived-full-group-is-finitely-presented` is still OPEN at 8b4ce1d3f.
- **Subsumption scan** (no truncation; "isolated", "marked group", and "colouring" together with "full group").
  - Item 1 of `fp-simple-groups-escape-soft-hyperlinear-permanence` (ESTABLISHED) already records f.p. ⇒ isolated for
    infinite simple groups. That is one direction of a lemma this node uses only in its consequence section.
  - `leavitt-unit-group-surjunctive` (OPEN) uses the same direction in prose and cites Cornulier–Guyot–Pitsch.
  - No older node states the pattern-model theorem.
- **Nits.**
  - The title says "the marked full group", but the theorem holds for every finitely generated `Γ ≤ [[Z^d ~ X]]`.
  - `d ≥ 1` is implicit in "free orbits are infinite".

## 10. Baumslag–Gersten claims (c6d492eb1): two PASS, one title narrowed

### 10.1 `baumslag-gersten-group-is-neither-linear-nor-self-similar`: PASS, title corrected forward

- **Item 1, recomputed** (route lines 12–25).
  - `ord(πb) = n`, and `(πb)^k πa (πb)^{-k} = (πa)^{2^k}`. At `k = n` this gives `n | 2^n − 1`.
  - For the least prime `p | n`, `ord_p(2)` divides `gcd(n, p − 1) = 1`. So `2 ≡ 1 (mod p)`, which is impossible,
    and `n = 1`.
  - `BG/⟨⟨a⟩⟩ = ⟨t⟩ ≅ Z`.
  - Known case: `BS(1,2)` maps onto `S_3` with `a` a 3-cycle and `b` a transposition, so `a` survives there. That image
    has `ord(πb) = 2 ≠ 3 = ord(πa)`, so it does not factor through `BG`. The route uses exactly this conjugacy.
- **Items 2–4.**
  - Magnus: `BG` is an HNN extension of `BS(1,2)` along the infinite cyclic `⟨a_0⟩ → ⟨a_1⟩`, so `a ≠ 1`.
  - Malcev gives item 3.
  - Level stabilizers of a locally finite rooted tree are normal of finite index with trivial intersection. That gives
    item 4.
- **Title overclaim.** "embeds in no rooted-tree automorphism group" is false without local finiteness. The rooted tree
  of depth 1 with countably many leaves has `Aut(T) = Sym(N)`, which contains every countable group. Body item 4 and
  the route both say locally finite.
  - **Corrected forward.** The title now ends "embeds in the automorphism group of no locally finite rooted tree".
- **Source re-read.** arXiv:2405.09722 Theorem 1.1 (MSI text `bh-reviewer/2405.09722.txt`, lines 29–30) concerns
  finitely presented self-similar groups, as cited.
- **Subsumption scan** ("gersten", no truncation, 38 hits).
  - Two OPEN nodes mention non-residual finiteness in prose: `baumslag-gersten-group-satisfies-boone-higman` and
    `one-relator-groups-satisfy-boone-higman`. So does the route `alekseev-thom-rips-flexible-p-instability-proof`.
  - No ESTABLISHED claim states it.
  - Item 4 is an instance of `self-similar-hosts-contain-only-residually-finite-groups`, as `distinct_from` says.

### 10.2 `baumslag-gersten-odometer-pieces-force-fixed-points`: PASS

- **Item 1** (route lines 12–28).
  - The structure theorem makes `a|Y` a rotation by `θ` with `Zθ` dense. Auslander, Chapter 3: source not re-read.
    The theorem is standard.
  - Then `b(x + nθ) = b(x) + 2nθ`. By continuity `b(k) = c + 2k`, and `b(−c) = −c`.
  - `a(t^{-1}y) = t^{-1} b(y) = t^{-1}y`. Only `b(Y) ⊆ Y` is used.
- **Item 2.** With `Y = X`, a minimal `a` on at least two points has no fixed point.
- **Item 3, recomputed.**
  - Ternary model: `2(x/2 + 1) = x + 2`, and `2 ∈ Z_3^×`. Sections on `d + 3Z_3` stay affine over `Z[1/2]`, because
    `m/2^j ∈ 3Z_3` iff `3 | m`.
  - Projective model: `Fix(a) = {∞}` and `Fix(b) = {0, ∞}`, while every `BG`-action has `Fix(b) = t·Fix(a)`. This
    obstruction does not use item 1.
- **Scope.** The node (line 34) and the route claim only `n = 2`. The route's `n = 4` example is right:
  `b(x) = 1 + 4x` on `Z_3` satisfies `b(x + 1) = b(x) + 4`, and it has no fixed point because `3x = −1` has no solution
  in `Z_3`. No drift toward general `n`.
- **Nit, title.** "odometer models of `BS(1,2)` never extend to the Baumslag–Gersten group" holds for extension on the
  same space, which is what item 3 says. On a larger space the induced action `BG ×_{BS(1,2)} Y` does extend the model.
  The route's proper-piece remark (lines 44–46) already allows this.
- **Subsumption scan** ("odometer", "adding machine", "equicontinuous", no truncation).
  - The ESTABLISHED hits are unrelated: `fpbs-line-independent-twisted-levels-disconnected` and
    `kazhdan-groups-without-fd-reps-violate-two-root-identity`.
  - No older node states the obstruction.
