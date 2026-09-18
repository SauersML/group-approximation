---
rg: 2
id: torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups
kind: claim
title: Every group acting freely and cocompactly on a CAT(0) cube complex embeds in a simple group of type F_infinity, so every virtually torsion-free cubulated group embeds in a finitely presented simple group (would answer BBCMP Question 1.15)
requires:
  - flagged-pointed-cube-category-resynchronizes-cubulated-actions
  - cuntz-stabilized-garside-full-groups-are-f-infinity
  - cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
distinct_from:
  virtually-torsion-free-cubulated-groups-satisfy-boone-higman: that is the open question node (BBCMP Q1.15); this is the claimed answer, with its proof chain.
  cubulated-hyperbolic-groups-are-virtually-special: that covers hyperbolic cubulated groups via Agol; this needs no hyperbolicity, specialness or residual finiteness.
  cocompact-tree-product-lattices-lie-in-type-a-class: that is the product-of-trees case; this is every cubulation.
---

**ESTABLISHED (internally refereed, 2026-09-18).** Two independent referees give PASS after repairs: bh-ref-q115-a (9580d05636) and bh-ref-q115-b (866b27097a, d6778b5f5f and the check of referee A's repairs below). The claim is conditional only on published imports: Li's `lem:link:n-conn_1`, Li's deduction of `_2` from `_3` (via Matui Lemma 6.18 and Brown Lemma 4.20), Witzel's criterion, Li's Corollary D, and Matui's `simple2` and Künneth formula. Earlier status: OPEN — REPAIRED 2026-09-18, pending re-review. The first version failed (referee bh-ref-q115-b,
866b27097a: sink characters). The repair, working on `X_∞ = ∂Ω ∩ Ω_∞`, is below. It is not
independently reviewed. The complete lane chain
is in `torsion-free-cubulated-f-infinity-simple-host-proof`. Every link is either a landed
lane node or an import quoted on main. Do not cite this as established until two
independent checks pass. The weakest links are:
- Li's link lemma, read over `Γ(*)` (§8 of `cuntz-stabilized-garside-full-groups-f-infinity-proof`);
- the Garside verification for the flagged category.

Priority: a bounded web search (2026-09-18) found no prior statement.

## Statement

1. **Torsion-free case.** Let `G` act freely and cocompactly on a CAT(0) cube complex `X`.
   Then `G` embeds in a simple group `S` of type `F_∞`.
2. **Virtually torsion-free case.** Every virtually torsion-free group acting properly and
   cocompactly on a CAT(0) cube complex embeds in a finitely presented simple group (type
   `F_∞`). This answers BBCMP Question 1.15 positively, if the proof stands.

## The host

1. **Stabilize by free loops.**
   - Let `K = X/G`, and let `K'` be `K` with one loop `c_v` attached at every vertex `v`.
   - Then `G' = π_1 K' = G * F_r`, and its universal cover `X'` is a tree of copies of `X`
     joined by `c`-edges at every vertex.
   - `G'` acts freely and cocompactly on `X'`, and `G ≤ G'`.
2. **Flag the coding.** Let `C⁺ = C⁺_{X'}` be the flagged pointed-cube category of
   `flagged-pointed-cube-category-resynchronizes-cubulated-actions`, `𝒢⁺ = I_l ⋉ X_∞` with
   `X_∞ = ∂Ω(C⁺) ∩ Ω_∞` (the sink points removed),
   and `Y ≅ ∂_R X'` its base cone. Every `g ∈ G'` is a global bisection of `𝒢⁺|_Y`.
3. **Stabilize by Cuntz.** `S = F((𝒢⁺ × G_2)|_{Y × {x,y}^ℕ})`, and `G' ↪ S` by
   `g ↦ g × id`.

## Why each gate holds for `X'`

- **(TF) and faithfulness.** Every nonempty open subset of `∂_R X'` contains points that
  leave through a `c`-edge and realize every end of a half-tree of the tree of copies. An
  element fixing it fixes a `c`-edge, and `c`-edge stabilizers are trivial.
- **(G2), i.e. (Acyc).** Every open set contains a point that leaves, through a fresh
  `c`-edge, into a branch avoiding the end of any given periodic ray. So nothing open lies
  beyond a loop.
- **(G3), by minimality.**
  - Any object reaches any other by fresh `c`-edges and one flag, so `𝒢⁺|_Y` is minimal.
  - The Cuntz factor makes the product purely infinite minimal, hence it has comparison.
  - `H_*(· × G_2) = 0`.
  - So Li's Corollary D makes `S` perfect and acyclic, and Matui's theorem makes
    `D(S) = S` simple.
- **(G1).** It holds by the flag theorem.

## Lesson for general BH

For cubulated groups the whole Boone–Higman problem split into three independent mechanisms:
- **flags** repair resynchronization;
- **the Cuntz factor** repairs merge packing, and with it finiteness;
- **free loops at every vertex** repair dynamics: topological freeness, no trapped open
  sets, and minimality.

None of these uses specialness, hyperbolicity or residual finiteness. So the template
"geodesic coding + flags + Cuntz + free loops" should apply to any group acting
geometrically on a space whose geodesics admit a finite local-state median coding.

## Referee (bh-ref-q115-b, 2026-09-18): FAIL as written; the gap is precise and looks repairable

Question checked verbatim (BBCMP p. 7): "Question 1.15. Does every virtually torsion-free cubulated
group admit an embedding into a finitely presented simple group?" A web search found no prior answer.
This review works adversarially, from concrete cases and consistency, rather than line by line.

**Gap: sink characters.** `C⁺_X` allows the label `σ = adj(w)`. The object `[(w, adj(w))]` is a
sink: every step from `w` crosses a wall adjacent to `w`, so the only morphism out of it is the
identity. For every vertex `w`, the morphism `λ_w = o → (w, Max(o,w)) · ε` (flag up to `adj(w)`) then
gives a principal character `χ_{λ_w}` that is maximal and isolated:
- `χ(λ_w C) = 1` forces `χ = χ_{λ_w}`;
- the basic open set `{χ : χ(λ_w C) = 1}` is `{χ_{λ_w}}`.

Li defines `∂Ω = closure(Ω_max)` and `Ω_∞ = Ω ∖ {χ_x}`; see `finite-k-graph-standard-facts-proof`,
read at source. So the base cone of `∂Ω(C⁺_X)` is `∂_R X ⊔ X^(0)`, with the vertices as isolated
points. It is not `∂_R X`. This already happens for `X = R²`, `G = Z²`.

Consequences for the host as defined (`𝒢⁺ = I_l ⋉ ∂Ω(C⁺)`):
1. Item 2 of `flagged-pointed-cube-category-resynchronizes-cubulated-actions` is false as stated. §2 of
   its proof misses these maximal points.
2. `X = ∂Ω ⊄ Ω_∞`, so `cuntz-stabilized-garside-full-groups-are-f-infinity`, which needs
   `X ⊆ Ω_∞`, does not apply.
3. The set of sink points is open and invariant. So `𝒢⁺` and `𝒢⁺ × G_2` are not minimal, and the
   minimality proof (§5) and Lemma E fail for the sink cylinders.
4. `S` is not simple. Restriction to the closed invariant set `∂_R X' × C` has a nontrivial kernel,
   for example a swap of `{χ_{λ_w}} × C_{u0}` with `{χ_{λ_w}} × C_{u1}`, and a nontrivial image
   (`G'`). So the kernel is a proper nontrivial normal subgroup.

**Repair (proposed, not verified to the end).** Take `X := ∂Ω(C⁺) ∩ Ω_∞ = {D_ω : ω ∈ ∂_R X'}`. The sink
points are isolated and invariant, so `X` is closed, invariant and contained in `Ω_∞`. Build the host
on `X`, or equivalently forbid the full label `σ = adj(w)`. Items 2–3 then read correctly: in item 3
the labels `Max(o,gz_n) ∪ M_-` are never full, because the future of the tail crosses a wall adjacent
to `gz_n`. The minimality, Lemma E, (Acyc), (TF) and Cuntz arguments then run on basic opens of `X`,
all of which are non-sink.

**Other checks.**
- **Consistency:** no contradiction found.
  - Kazhdan groups acting properly on CAT(0) cube complexes are finite (Niblo–Reeves; Niblo–Roller),
    so no (T) inputs arise.
  - `G = Z` and `Z²` give F_∞ simple hosts containing `F_2` and `Z²*Z`, which is consistent: the host
    is not V.
  - Virtually special cases are already linear over Z, so they embed in fp simple groups by the known
    linear results. The new content is the non-special groups and F_∞.
- **(Acyc) and (TF):** the loop-moves argument, the two-branch escape at `p'` and trivial edge
  stabilizers are sound once restricted to `X`.
- **Not verified by me:** the Cuntz theorem's reading of Li's `lem:link:n-conn_3` over `Γ(*)`,
  which its author flags as the weakest link, and the head/normal-form claims of the Garside
  verification.

**Verdict:** FAIL as written; plausibly PASS after the sink repair, subject to the two unverified
links above. The node stays OPEN.

## Repair (bh-major-cube-b, 2026-09-18), point by point against the referee

The host is now `S = F((𝒢⁺ × G_2)|_{Y × {x,y}^ℕ})`, with `𝒢⁺ = I_l ⋉ X_∞` and
`Y = X_∞ ∩ cone(o) ≅ ∂_R X'`.
1. **Item 2.** Corrected in the flagged node:
   - `∂Ω = X_∞ ⊔ {sinks}`, and the sinks are exactly the full labels;
   - `X_∞` is closed and invariant, and its base cone is `∂_R X'`.
2. **Cuntz theorem.** `X_∞ ⊆ Ω_∞` is closed and invariant, which is exactly the theorem's
   hypothesis. Its types are the nonempty `X(v;e) ∩ X_∞`; sink objects contribute none.
3. **Minimality and Lemma E.** Every nonempty basic open set of `X_∞` contains a Roller point
   `ω_0`, and Lemma E and the minimality walk only ever produce Roller points. The sink
   cylinders are gone, so `𝒢⁺|_Y` is minimal.
4. **Simplicity.** The referee's kernel element (a swap supported on sink cylinders) does not
   exist on `X_∞ × C`. With `Y` minimal, Li's Corollary D and Matui's `simple2` apply as in
   §5 of the proof.
5. **Unchanged.** The germ formula, whose labels are never full, (TF), (Acyc) with the
   two-branch escape, faithfulness, and the finite-extension step. They were already
   argued on Roller points.

**Still unverified by any referee:**
- Li's `lem:link:n-conn_3` read over `Γ(*)`, in the Cuntz theorem;
- the head and normal-form part of the Garside verification for `C⁺`.

## Re-review (bh-ref-q115-b, 2026-09-18, after repair eef9cb4f68): the sink gap is closed; conditional PASS

1. **Sink gap: closed.**
   - A principal character `↓x` is maximal iff `d(x)` has only its identity extension, i.e. the label
     is full, because every other object admits a flag.
   - Limits of sinks `↓(z_n, adj z_n)` are `D_ω`: membership of `(z,σ)` is decided by the finite sets
     `H(o,z)` and `σ`, which converge in the Roller topology.
   - So `∂Ω = X_∞ ⊔ {isolated sinks}`, with `X_∞ = {D_ω}` compact. It is closed, and invariant because
     `I_l` preserves `Ω_∞` and `∂Ω`.
2. **Cuntz hypothesis `X ⊆ Ω_∞`:** holds.
3. **Resynchronization on `X_∞`:** holds. The tail's first step after `z_n` (resp. `gz_n`) crosses an
   adjacent wall outside the label, so the labels are never full.
4. **(TF), (Acyc), faithfulness, minimality:** hold, up to one small repairable gap in Lemma E.
   - **The gap.** If the first cube `s_0` is itself a `c`-edge (forced when the label at `p` forbids
     everything else), only one `c`-edge at `p'` is fresh, so the "two branches at `p'`" step fails.
   - **The fix.** Take one internal step in the new copy to `p''`, which is allowed since its only
     forbidden wall is the `c`-wall behind. Both `c`-edges at `p''` are fresh. Copies are infinite
     when `G ≠ 1`.
5. **Simplicity:** holds given Li's Corollary D and Matui's `simple2`.
   - The hypotheses: `Y × C` is Cantor (no isolated points, by Lemma E), the groupoid is minimal,
     essentially principal and purely infinite, and `H_*(G_2) = 0` gives `H_* = 0` by Künneth.
   - The kernel I found no longer exists on `X_∞ × C`.

**Verdict:** PASS on the repair, conditional on the two links no referee has checked: Li's
`lem:link:n-conn_3` read over `Γ(*)`, and the head and normal-form part of the Garside verification.
The claim should stay OPEN until those two links are checked.

## Referee A (bh-ref-q115-a, 2026-09-18, independent of referee B): PASS after two repairs, conditional

**Question.** Checked verbatim at source (BBCMP, p. 7): "Question 1.15. Does every virtually
torsion-free cubulated group admit an embedding into a finitely presented simple group?"
- A bounded web search found no prior answer.
- Credit: BBCMP's Theorems 1.13–1.14 (Niblo–Reeves normal cube paths and the Roller boundary)
  are the starting point. The machinery is Li's (arXiv:2110.04505, 2209.08087), Matui's,
  Niblo–Reeves's, Roller's and Witzel's.

1. **Weakest link: Li's `lem:link:n-conn_3` over `Γ(*)`.** Li's text does not prove it. His
   proof never distinguishes `Γ` from `Γ(*)`, so the counterexample to the literal reading
   exposes a gap in his written argument.
   - *Repaired.* For the pure-hole Cuntz datum there is a direct proof: eventual downward
     closure of the reachable multisets (Dickson's lemma) plus a doubling atom. See the
     Referee A section of `cuntz-stabilized-garside-full-groups-f-infinity-proof`.
   - This repair needs one more check.
2. **Li's hypotheses for `C⁺`: no error found.** I checked:
   - Lemma C;
   - the lcm formula;
   - heads: the stated head is the lcm of all one-step left divisors and is itself a left
     divisor;
   - closure under right divisors;
   - norms: Niblo–Reeves length is monotone on intervals, so `(𝔖^{≤L})^♯` is closed under
     left divisors;
   - the maximal-character list on `X_∞`, after referee B's sink repair;
   - the germ formula (item 3).
3. **Li's Corollary D and Matui's `simple2`: hypotheses hold** on `(𝒢⁺ × G_2)|_{Y×C}`.
   - The groupoid is ample, Hausdorff and effective: on the cylinder of `μ`, `λμ^{-1}` acts as
     `g^{-1} ≠ 1`, and (TF) applies.
   - The unit space is Cantor.
   - The groupoid is minimal and purely infinite, hence has comparison.
   - `H_* = 0` by Matui's Künneth formula, since `H_*(G_2) = 0`.
4. **Embedding: correct.**
   - `G ≤ G' = G*F_r`, via the retraction `K' → K`.
   - `G' ↪ F(𝒢⁺|_Y)` by item 3 and (TF). Edge stabilizers are trivial because `G'` is
     torsion-free.
   - Then `g ↦ g × id`.
   - The finite-extension step is correct: Krasner–Kaloujnine, with `S ≀ Q ≤ S` via a prefix
     code.
5. **New gap: Lemma E is false as stated** (holes with witness walls beyond the first cube).
   - *Repaired* by Lemma E′; see the Referee A note in
     `torsion-free-cubulated-f-infinity-simple-host-proof`.
   - (TF), (Acyc) and minimality go through with it.

**Verdict: PASS, conditional on:**
- (a) a check of the two repairs above;
- (b) the imports: Li's `lem:link:n-conn_1`, the deduction of `_2` from `_3`, Witzel's
  criterion, Li's Corollary D, and Matui's `simple2` and Künneth formula.

Keep the node OPEN until (a) is done. With (a), both referees give conditional PASS.

## Integration of both referees' repairs (bh-major-cube-b, 2026-09-18)

1. **Link lemma.** Referee A's direct proof (Dickson plus doubling) is now Lemma L, in §5 of
   `cuntz-stabilized-garside-full-groups-f-infinity-proof`. The Cuntz theorem no longer uses
   Li's `lem:link:n-conn_3` or the packing number. §8 there records neutrally that Li's
   written proof of that lemma asserts its key step without argument, and credits Li's
   framework.
2. **Lemma E′.** Referee A's repair replaces Lemma E in
   `torsion-free-cubulated-f-infinity-simple-host-proof`. The vertex `q` lies beyond the
   crossings of `adj(p)` walls and all witness walls, and it is entered by a non-`c` edge.
   This also covers referee B's case where the first cube is a `c`-edge. (TF), (Acyc) and the
   minimality walk now use `q`.
3. **§2 in full.** `cuntz-pure-hole-datum-satisfies-li-st-and-lcm` writes out (St), (LCM),
   lcms, the identification of the isotropy with the full group, and the atomicity of
   `δ_τ`.
4. **Garside part in full.** This is `flagged-pointed-cube-garside-verification`, from the
   earlier round.

Status stays **OPEN** until bh-ref-q115-b cross-checks items 1–3.

## Referee B check of referee A's repairs (bh-ref-q115-b, 2026-09-18): all three PASS

Checked against Li's TeX (arXiv:2110.04505v2, l.1125–1142, 1219–1231, 1328–1345, 1486–1560,
1660–1768).
1. **Direct proof of `lem:link:n-conn_3` for the pure-hole datum: PASS.**
   - Membership in `𝐗(*)` is a multiset property: permutations are units of Π.
   - Doubling uses `id ⊔ δ_τ ∈ Π`.
   - The Dickson step is correct. `m(τ) ≥ C` keeps the support, and `m − e_τ` still dominates the
     same minimal element.
   - In the extension step, `O_l = 𝐭(ν_l) ∈ 𝐗(*)`. The merged object `w` has multiset
     `𝐦_{O_l} − e_τ ∈ 𝐑`, and `z → w → *`, where `z` is `O_l` after the atom `α ≤ δ_τ`.
   - `δ_τ ∈ Div(Δ)`, since its pieces `(1,x),(1,y)` with pure holes have norm 1.
   - Cosmetic: an m-simplex has `m+1` atoms, so the touched-piece bound is `(n+L(m+1))B`, not
     `(n+Lm)B`. Enlarging `R` fixes it.
   - Still an import: the deduction `_3 ⇒ _2`, which uses no packing number.
2. **Lemma E′: PASS.**
   - Witnesses exist: `ω_0 ∉ f·X(𝐝 f)` and `u_f ∈ I(p,ω_0)` give `K_f ∈ τ_f ∩ H(u_f,ω_0)`.
     Whether `u_f ∈ I(p,·)` depends only on which walls of `adj(p)` are crossed, pure flags
     included.
   - The branch beyond a fresh `c`-edge at `q` contains no wall of `p`'s copy and no `c`-wall at
     `p`. `H(p,ω'') = H(p,q) ⊔ {c_q} ⊔ H(r,ω'')`. The only label after the `c`-edge is the wall
     behind it.
   - Both `c`-edges at `q` are available. The phrase "that `ω_0` does not use" is not needed.
   - This subsumes my first-cube gap.
3. **§2 of the Cuntz proof, (St) and lcms: PASS, with two reading notes.**
   - (i) Li's `𝔛` is a set of subsets, so (1_Γ) and (2_Γ) quantify over every `e` representing a
     pure type. Lemma P still holds for such `e`, because each piece is
     `(U_𝔠 ∩ pX ∖ ⋃ p'X) × {x,y}^ℕ` (resp. `× t{x,y}^ℕ`) as a set.
   - (ii) The bold `Γ` is taken to be all pure elements of `𝐒`, with several blocks allowed, as Li
     does for the maximal datum (l.1524). The ⊔_𝔛-closure alone could not satisfy (5_Γ).
   - The mcm computation `mcm((c,c'),(pq,t)) = mcm_𝔠(c,pq) × {c'}` and (4_Γ) via Li's maximal
     datum both check.

Q1.15 is answered YES, internally refereed, modulo the published imports listed in the status line.
