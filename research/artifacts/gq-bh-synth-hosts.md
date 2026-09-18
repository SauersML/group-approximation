# Host-side synthesis for general Boone–Higman (bh-synth-hosts, 2026-09-18)

This file distills the host results that landed on 2026-09-18 into one machine, the slots through which inputs can enter it, and the barriers that separate the inputs we reach from the hard ones. It ends with the host theorems whose proof would move the general conjecture. Everything cited is a lane proof unless marked otherwise.

Two new theorem nodes land with this file:
- `rank-one-cone-hosts-put-fw-groups-in-local-map-groups`, with its proof route;
- `finitely-coded-unit-groups-act-residually-finitely`.

## 1. The machine

Every host built today is, up to taking subgroups, a topological full group `F(𝒢)` of an ample groupoid `𝒢` on a Cantor space. So the permutational form of BH (B_A) reduces to two inputs:

- **(M1) A coded action.** The input acts faithfully by bisections of `𝒢`.
- **(M2) Finite presentation.** The full group of `𝒢 × O_2` (Cuntz-stabilized) is finitely presented.

Everything else is automatic.
- **Type (A).** `𝒢 × O_2` has comparison on each piece: refine, duplicate with the O_2 colour, and equalize counts. So a finitely presented stabilized full group acts with type (A) on clopen sets (`finitely-coded-cantor-actions-give-type-a-hosts`, bh-lattices 209c5dbe1, and the degree-category and k-graph nodes).
- **The general equivalence** is already on main: B_A is the class of subgroups of finitely presented full clopen-transitive Cantor hosts (`permutational-boone-higman-iff-full-cantor-hosts`).

**The engine behind (M2)** is always a Stein–Farley complex whose descending links are highly connected: Witzel's criterion inside Li's Garside-category theorem (arXiv:2110.04505, Theorem `thm:Fn`; Zappa–Szép version `thm:ZS` and Example `ex:ZS`, read at source by several lanes). Li needs:
- finitely many objects;
- a locally finite transverse Garside family, i.e. finitely many splitting shapes up to units;
- existence of lcms, condition (F) (faithful units) and condition (St);
- unit groups `ℭ*(v,v)` of type F_n.

Every other finiteness proof used today specializes, or runs parallel to, this one:
- Belk–Zaremsky's for `SV_G`;
- BBMZ's nucleus argument for contracting RSGs;
- Nekrashevych's for expanding self-coverings;
- Belk–Hyde–Matucci Theorem 2.1 for germ extensions of V, which is the relative version.

| host family | splitting category and its rank | local maps / units | engine |
|---|---|---|---|
| `V`, `V_{n,r}`, SFT and graph full groups | path category of a finite graph; rank 1 | trivial | Li / Matui |
| `nV` | cube category; rank n | trivial | FMWZ / Li |
| Röver–Nekrashevych `V_d(H)` | free monoid ⋈ H; rank 1 | H, synchronous | Li (ZS III), Nekrashevych |
| Katsura / Exel–Pardo, `2V_τ` | graph ⋈ Z; rank 1, or 2 after Cuntz | odometer | Li (ZS) |
| `CT_P(Z)` | one-vertex k-graph, `k = |P′|` | trivial | Li `cor:OneVertex` |
| tree-product and Ã₂ lattices | Zappa–Szép k-graph (cubes or tiles); rank = number of factors, or 2 | finite stabilizers | Li (ZS III) plus power and phase |
| contracting RSGs (hyperbolic groups, Pisot Stein groups) | SFT cones; rank 1 | rational (asynchronous) nucleus | BBMZ |
| `SV_G` | cube category on `C^S`; infinite rank | the actor G permutes directions | Belk–Zaremsky |
| `W`, `W_(P,ℓ)` | halving along directions in `D`; infinite rank | F permutes directions | Belk–Zaremsky transfer |
| germ extensions of V (recoding, shells, Houghton-like) | V plus finitely many singular orbits | germ groups | BHM Theorem 2.1 |
| `𝒯_m`, `2V_Λ(n)` for `m, n >= 2` | unimodular or Lagrangian dissections; **not LCM** | — | **none**: the open gate |

## 2. The slots through which an input enters

An input `G` can sit in `F(𝒢)` in four ways.

- **(U) Units / local maps.** `G` acts cone to cone through the local-map groupoid, like `H` in `V_d(H)`, or like the local actions of an RSG.
- **(P) Piecewise elements.** `G` is spread over bisections that are not units. Examples: hyperbolic groups in their RSG, lattices in k-graph full groups, `V` inside itself.
- **(T) Twist.** `G` permutes infinitely many splitting directions (`SV_G`, `W`). This requires `G`, or an overgroup of it, to already have a type (A) action on the directions, so it is circular for BH: it gives closure theorems, not new inputs.
- **(S) Singular germs.** `G` is carried by the isotropy at finitely many singular orbits of an otherwise finite-data groupoid. Examples: BHM, shells, Houghton-like envelopes.

**New theorem 1** (`finitely-coded-unit-groups-act-residually-finitely`). In every finitely coded groupoid, of any rank, each unit group acts on its object boundary through a residually finite group. The reason: units permute the finitely many cylinders of each degree, and those cylinders separate points.

- **The unit slot is residually finite.** This generalizes `self-similar-hosts-contain-only-residually-finite-groups` from regular trees to every coded groupoid.
- **Consequence.** The inputs carrying the conjecture are infinite simple groups (`boone-higman-iff-infinite-simple-inputs`). They cannot be units; they must sit in (P), (S) or (T).

**New theorem 2** (`rank-one-cone-hosts-put-fw-groups-in-local-map-groups`). Take any full group whose cones form a tree and whose local maps form a self-similar groupoid Λ.
- **Statement.** Every FW (for instance Kazhdan) subgroup virtually embeds in a finite power of Λ's vertex groups. An infinite simple FW subgroup embeds in a single vertex group.
- **Mechanism.** Deep cones are sent to cones, so the set of cone markings is commensurated. FW transfixes it, and a finite invariant cover by marked pieces reads off local maps.
- **Coverage.**
  - It recovers the Röver–Nekrashevych Kazhdan theorem (synchronous Λ).
  - It gives finiteness of FW subgroups for `V`, `V_{n,r}` and all graph full groups (trivial Λ), and for Katsura odometers.
  - Together with `almost-v-fw-subgroups-act-through-finitely-many-germs` for singular points, it covers all rank-one host families on main.

**Rank one is local.** In a rank-one host, whether through cones or through finitely many singular points, a Kazhdan input is always carried by a local group: a unit or local-map group, or a germ group. Rank-one constructions can therefore only relocate a simple Kazhdan input into a local group; they cannot create room for it. That is the common reason behind today's closures:
- the Röver–Nekrashevych route died (`boone-higman-via-rover-nekrashevych-hosts`);
- V-germ extensions in the normal regime have only finite Kazhdan subgroups;
- window-zero shells fail for FW inputs (bh-free-33, bh-kazhdan-inputs, gq-typeA-design);
- the gate for St_N(R_L) is always "a Kazhdan group inside one germ group".

## 3. What separates reachable inputs from hard ones

Five barriers account for every obstruction landed today. Each is a property of the local data, and a host can only beat it by changing that data.

| barrier | mechanism | kills (inputs, in which hosts) |
|---|---|---|
| **RF** | unit and synchronous local groups act on finite level sets | non-RF inputs in the unit slot: Deligne, `Q_{g,c}`, `St_N(R_L)`, simple groups, the 2609.01868 wreath (dense cosets) |
| **Rank** | tree cones make cone markings commensurated, so FW transfixes them | Kazhdan inputs in rank-one hosts, unless the local maps already contain them: Deligne, `Q_{g,2}`, `PE_N(R_L)`, Titz–Witzel kernels, all reduced inputs |
| **Complexity** | finite data bounds the word problem: exponential for finite units (`finite-k-graph-full-groups-have-exponential-word-problem`), coNP for `nV`, one counting quantifier for Leavitt tensors | universality of every fixed finite-data family; BH forces unbounded complexity, which must enter through residually finite units, germ groups or twists |
| **Scale** | the degree / slope monoid is finitely generated; masses are a f.g. `Z[1/d]`-module; roots are bounded at hyperbolic periodic points; no common tree coding of rotations and doubling; `ℓ`-adic scalars can't be prime-shifted | `Q`, `Aff(Q)`, `GL_n(Q)` and `Q ⋊ ⟨2⟩` in every host whose primes must come from the degree part (bh-free-16, bh-free-30, bh-free-31, bh-universal) |
| **Dynamics / growth** | a Baumslag–Solitar base has zero entropy and logarithmic movement; homogeneous invariants vanish on BS bases; bases are never loxodromic | H4 and BG in brick hosts, in proper cocompact CAT(0) hosts, and in isometric-brick hosts |

The hard inputs sit where two barriers meet:
- **The reduced inputs** (simple Kazhdan with solvable WP): RF plus Rank, so they need **(P) in rank ≥ 2**, or asynchronous local groupoids that already contain them.
- **GL_n(Q)**: the Scale barrier, so the primes must be carried by units, equicontinuous directions or infinitely many independent directions (twist), never by the degree monoid. bh-free-30: hosts for `GL_n(Q)` need infinitely many independent scaling ratios not tied together by a self-similar map.
- **Deligne and `Q_{g,c}`**: RF plus Rank, plus a central class that survives on point stabilizers, so boundary-built hosts can't untwist it (`central-extension-untwisting-over-boundaries`). So **(P) in rank ≥ 2 with a genuinely twisted cover**.
- **H4 and BG**: the Dynamics barrier. Brick hosts need a renormalization that is not isometric; CAT(0) is excluded.

## 4. The master host program

**Master reduction (host side).** Suppose every infinite finitely generated simple Kazhdan group with solvable word problem acts faithfully by bisections of a finitely coded groupoid of rank at least 2, or through an asynchronous local groupoid, and the stabilized full group is finitely presented. Then the general conjecture holds, by the machine of section 1 and `boone-higman-iff-simple-kazhdan-decidable-inputs`. By the two new theorems, no rank-one synchronous version of this statement can hold: the hypothesis must be met in rank at least 2 or asynchronously.

Three concrete host theorems would move the general conjecture most, in order of leverage.

1. **A Li theorem without lcms.** Prove finite presentation (F_2 is enough) for full groups of *dissection categories*: splitting categories whose pieces meet in non-principal intersections. Examples are unimodular simplicial cones in `R^{m+1}` and Lagrangian signature cells.
   - **What it would give.** It would settle `rational-projective-full-groups-are-finitely-presented` for `m >= 2`, and hence Boone–Higman for closed mapping class groups (BBMZ 5.3(2), via `𝒯_{6g-7}`). It would also settle `lagrangian-brin-thompson-group-is-finitely-presented`, and hence Deligne's lattice via `2V_Λ(n)`, which is rank ≥ 2 and so escapes the Rank barrier.
   - **Why it's the top priority.** Both targets are stuck on exactly this missing engine (bh-free-54: not right-LCM; bh-free-55: three-frame regions are not finite unions of cells).
   - **Suggested tool.** Stein–Farley complexes on dissection posets, with descending links controlled by a weak-factorization theorem (Morelli–Włodarczyk) in place of Garside normal forms.
   - **Correction (bh-free-55, f86da7972).** This item overstated the Deligne half. `maslov-cantorizations-have-no-finite-dissection-type` shows that at n = 2 no Sp_4(Z)-invariant Maslov Cantorization has finite dissection type: rational light cones meet at corners defined over Q(√2p) for every odd prime p. So no pair-diagram engine, dissection-category theorem included, can prove 2V_Λ(2) finitely presented. `deligne-class-dies-over-flag-varieties-iff-flag-has-lagrangian` adds that the lift exists only over flag varieties containing a Lagrangian, never over spaces with an invariant measure. The split is:
     - **Rational corners (hyperplane or coset walls):** `𝒯_m` for closed MCG, and W for GL_n(Z). A dissection-category theorem still covers these.
     - **Deligne's lattice:** needs one of a non-algebraic Γ-equivariant recoordinatization of Λ with rational corners, a piecewise-linear Sp_2n(Z) inside `𝒯_m` that kills the class (`deligne-class-dies-on-some-rational-projective-host`), or a finiteness theorem that doesn't use diagrams.
     Simplicity is free for all of these hosts (`cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple`), so finite presentation is the whole gate.
2. **Germ extensions of higher-rank hosts.** State and prove a BHM Theorem 2.1 for finite germ extensions of `2V`, or of a k-graph full group, at finitely many singular points or singular lines.
   - **Why.** Rank-one locality kills Kazhdan inputs in V-germ extensions only because V's cones form a tree. Over `2V` the cone markings are not commensurated, so a Kazhdan germ group is not forced to be local.
   - **Test cases, in order:** `PE_N(R_L)` for the GL_n(Q) route; Deligne; `Q_{g,2}`.
3. **Asynchronous rank-one hosts.** For a simple Kazhdan `S`, a rank-one host exists only if `S` lies in the local-map groupoid of a rational similarity structure. So the rank-one question for `S` is exactly: does `S` itself carry a faithful RSG action whose full closure is finitely presented? This is BBMZ-hyperbolic Q1.4 applied to `S`; bh-higman-classic shows the full closures are acyclic in the V-normalizer test family. It is a cleaner target than shells, but it needs asynchronous dynamics on `S` itself.

**What to stop.** Designs that put a Kazhdan input into a rank-one synchronous structure:
- window-zero shells;
- normal-regime V-germ extensions;
- Röver–Nekrashevych or Exel–Pardo hosts;
- rank-one Houghton-like near actions.
These can only reproduce "input inside one local group" with no new finite presentation.

**What the machine already gives for free**, and should be used rather than rebuilt:
- type (A) and comparison after Cuntz stabilization;
- product, graph-product and finite-extension closures in B_A;
- undistortion of locally faithful actors (bh-free-45);
- `F_n` of `SV_Γ` equivalent to (A_n) (bh-typeA-universal).

## 5. Lessons (also posted to board/LESSONS.md)

- **The one machine.** B_A = (faithful coded action) + (finite presentation of the stabilized full group). The only analytic input is a Stein–Farley descending-link argument; Li's theorem is the general form.
- **Units are residually finite.** In every coded groupoid the unit groups act residually finitely. Simple inputs must be non-unit elements, and a host's complexity can only be imported through residually finite units, germ groups or twists.
- **Rank one is local.** In rank-one hosts, FW inputs sit inside local groups (local maps or germs), so for Kazhdan inputs rank ≥ 2 or asynchrony is forced.
- **The top gate.** A finiteness theorem for non-LCM dissection categories with rational corners is the missing engine behind closed MCG (`𝒯_m`). It cannot reach Deligne through `2V_Λ(n)`: Maslov Cantorizations have no finite dissection type (bh-free-55, f86da7972), so Deligne needs a finiteness proof that doesn't use diagrams, or a recoordinatization with rational corners.
