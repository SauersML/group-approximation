# gq critic pass 2 (2026-09-18)

Lane `gq-critic`. Read: the root's Attempts 1–18, all 69 boards, and the status line of every gq claim node on
origin/main (about 180 ESTABLISHED, 49 OPEN, 3 REFUTED). Critic only: no claims of my own. Node ids are backticked.

**Correction to pass 1.** Pass 1's gap G1 ("FW for SL_n(Q) would kill the RN, RSG and cube-complex germ hosts") is
settled the other way. By `sl-n-q-lacks-property-fw` (Serre), SL_n(Q) is countable and not finitely generated, so it
has no FA and hence no FW. The FW method survives only through its finitely generated Kazhdan pieces, i.e.
`gl-n-q-almost-v-hosts-need-lattice-germs`.

## 1. Host families never tried

"Tried" means that some node or board attempt addresses the family. Families 1–4 are untried or touched only in
sparks; family 5 is tried but closes only inside BLIW.

1. **Complexes of groups over the restricted-product (adelic) building.**
   - `sl-n-q-is-colimit-of-lattice-stabilizers` (ESTABLISHED) makes SL_n(Q) the colimit of lattice stabilizers
     ≅ SL_n(Z) over the restricted product ∏'_p of Bruhat–Tits buildings.
   - The action has one vertex orbit, i.e. it is cocompact, and its vertex groups are finitely presented. For n ≥ 3
     they are Kazhdan and lie in `B_A` (Scott). But the complex is not locally finite.
   - For n = 2 it is the median graph ∏'_p T_p (gq-sl2q spark, never pursued). The action is not proper, so
     `proper-semisimple-cat0-groups-contain-no-gl-2-q` does not apply; FA fails, so fixed-point kills do not apply
     either.
   - No permanence or envelope theorem exists for complexes of groups that are cocompact, not locally finite, and
     have fp vertex groups. BLIW needs locally finite trees and fp edge stabilizers. This is the natural
     "graph of groups over nontrivial edges" host and it is untouched.
2. **Twisted Brin–Thompson SV_Γ over non-ring actors that contain all of GL_n(Q).** Tried:
   - actors that are f.g. subgroups (`fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups`);
   - prime-shift actors K_n and A_1 (gq-deep-typeA-2: fp and a f.g. stabilizer both open);
   - RN actors V_p(Γ_p) (gq-rn-varying-degree).

   Never tried:
   - (a) The fp group St_N(R_L) as an actor. It contains every GL_n(Q)
     (`one-steinberg-group-contains-every-gl-n-q`, triple-refereed), is Kazhdan (Ershov–Jaikin-Zapirain–Kassabov for
     f.g. rings), and is fp in rank ≥ 5 (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`). Its
     natural actions have K_2-type kernels, so the gate is `abstract-btb-simple-quotient-fp-gate`. A faithful type
     (A) action of St_N(R_L) itself was never examined. Its solvable word problem, i.e. decidability of membership
     in K_2(N,R_L), was never examined either. Solvable WP is what makes St_N(R_L) a Boone–Higman input.
   - (b) Actors that are themselves Thompson-type groups containing Q (kV, 3V ⊇ BS(1,3)) acting on non-Cantor
     orbit sets.
3. **Groupoid (Nekrashevych/Matui) groups of the solenoid with all primes.** Only the ring side is done
   (`af-groupoid-rings-have-no-fg-subring-containing-q`).
   - No lane built a topological full group or Nekrashevych group whose isotropy carries the Aff configuration,
     e.g. from the ×p maps together with translations on the full solenoid dual to Q.
   - The dyadic case (baker map = ×2 on Σ_2 ≅ C × Z_2, inside 2V) is a gq-deep-typeA-1 spark.
   - gq-pp-simple names the Nekrashevych A(G) exit: it is simple, and f.g. when the germ groupoid is expansive.
4. **The rational group R and Aut(V).**
   - R contains (Q,+) via T̄ and BS(1,2) (gq-deep-free-3 sparks), so it escapes O3/O4, and it contains every RSG.
   - Nobody has tested Aff(Q) ≤ R or Aff(Q) ≤ Aut(V) (gq-explicit-2 spark S1). This is the cheapest decisive test
     for all of M5 (RSGs): a no kills RSGs; a yes gives a target.
5. **Graphs of groups with divisible edge groups.**
   - *Not a gap in G itself.* `extension-product-closures-cannot-create-sl-n-q` puts every solvable group in P_n.
     So mapping tori and HNN extensions over divisible edges (Aff⁺(Q) = Q ⋊ ⊕Z is such a tower) can create Aff(Q)
     but never SL_n(Q).
   - For SL_n(Q) the edges must be non-abelian: Ihara's `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell` has
     Iwahori edges.
   - BLIW's hypothesis (fp edge stabilizers) excludes every divisible edge group by definition, so a new permanence
     theorem would be needed. Family 1 is the better-posed form of this.

Also untried, but lower value:
- higher-dimensional non-Cantor spaces with Z-covers (flag bundles; gq-pp-higher spark);
- Cremona-type bijections of P^{m-1}(Q) in the Zariski topology (gq-typeA-projective spark);
- Burger–Mozes-style lattices acting non-properly with infinite vertex stabilizers.

## 2. The sharpest open gates, ranked

1. **`bs12-embeds-in-brin-thompson-2v`.**
   - *What it gates.* Every Thompson-register route to n ≥ 2 (`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`).
   - *Progress.* BS(1,3) ≤ 3V is established (the SMART induced map, exact tripling). One-head move hierarchies
     cannot give 2, by the parity lemma (`crossing-move-hierarchies-have-odd-branching`).
   - *Sharper forms.*
     - BS(1,2) via two heads or via an even-arity odometer code (`renormalizable-thompson-elements-are-odometer-codes`).
     - The joint test: BS(1,2) and BS(1,3) with commuting stable letters in one kV, i.e. Aff(Z[1/6])⁺-type.
       Aff(Q) needs every prime at once.
2. **`rational-iwahori-group-lies-in-fp-self-similar-group`.**
   - *What it gates.* PSL_2(Q) through `psl2-q-fp-simple-via-rational-iwahori-rn-host`. The input
     PGL_2(Q) ≤ V_p(Γ_p) is established.
   - *Why it's sharp.* It is one fp-self-similar question about an RF countable group, and O1 does not bite.
     Λ must be non-contracting, non-Möbius and non-linear.
3. **The one-prime-left-out fp RF gate:** `resolvent-steinberg-group-is-residually-finite`, with
   `z-localized-embeds-in-fp-rf-group`, `sl-2-z-localized-has-fp-hecke-overgroup` and `rf-resolvent-elementary-group-is-fp`.
   - One explicit fp Kazhdan group, St_N(R_l) ⊇ Z_(l), where residual finiteness is decisive for both the BLIW
     route to SL_2(Q) and the self-similar route.
   - Rauzy-type obstructions do not apply, since Z_(l) is effectively RF.
4. **`regular-germ-extensions-have-no-bs-relations`.** This is a kill gate: it would close n = 2 in the whole
   regular germ regime. gq-va-gl2 isolated the exact remaining germ type (infinite order, depth-gain zero).
5. **`pgl-q-projective-type-a-extension` in its strong form, for the explicit prime-shift groups K_n and A_1.**
   - What remains: injectivity of Π_1 → A_1, finite presentation of A_1, and a f.g. point stabilizer.
   - These questions live only in root Attempt 18. **Recommend landing them as OPEN nodes.**

Not sharp, because each is equivalent in strength to the root:
- `rational-leavitt-simple-group-embeds-in-fp-simple-group`;
- `psl-n-q-maps-nontrivially-to-fp-simple-groups`;
- `sl-odd-q-has-fp-just-infinite-host`;
- `gl-n-q-in-permutational-boone-higman-class`;
- `countable-decidable-groups-embed-in-fp-simple-groups`.

## 3. Is there a meta-theorem? Yes, three are worth stating as claims (each an assembly of landed nodes)

**MT-A. Localization, or "no base case".**
- *Scope.* H is finitely generated and is either locally in a finitely generated base L of piecewise maps off a
  closed nowhere dense or finite set, or almost-V, or a lift, or a circle/line group, or a group of almost
  automorphisms of a tree.
- *Statement.*
  - For n = 2, every embedding of Aff(Q) puts a nontrivially normalized divisible (Q,+) into one local group: a
    piece group, a point-germ group, or the germ group at infinity.
  - For n ≥ 3, every embedding of the chain SL_3(Z[1/m]) puts finite-index subgroups of all of them into one
    singular germ group.
  - So H hosts GL_n(Q) only if one of its local groups hosts the same configuration.
- *Every landed class of local groups fails:* f.g. linear or RF (Mal'cev), divisible-free, T̄/VA-pattern,
  rational-slope PL (no Heisenberg), eventually periodic or aperiodic tree germs, normal/finite-index germs over V.
- *Inputs:* `pp-circle-divisible-subgroups-act-freely`, `circle-groups-with-divisible-free-germs-omit-gl-n-q`,
  `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`, `germ-extensions-omit-standard-gl-n-q`,
  `periodic-point-germ-groups-omit-aff-q`, `commensurating-end-germ-groups-omit-aff-q`,
  `rational-slope-germ-groups-have-bs-but-no-heisenberg`, `normal-germ-extensions-of-thompson-v-contain-no-sl3z`,
  `almost-v-fw-subgroups-act-through-finitely-many-germs`, `gl-n-q-almost-v-hosts-need-lattice-germs`,
  `aperiodic-tree-almost-automorphism-fg-subgroups-are-rf`, `type-a-orbit-accumulation-forces-fg-nontrivial-germs`.
- *Consequence.* A germ-type fp host must implant, as a germ group, an fp group that already contains the
  configuration. Such fp groups exist (St_N(R_L), the answer to Problem 2.7). So the germ question becomes "implant
  St_N(R_L)-type germs and keep finite presentation" (BHM Theorem 2.1 needs fp germ stabilizers). This is the
  repo's shell route (`decidable-inputs-have-fp-shell-stabilizers`) specialized to one structured input, and nobody
  has tried it.

**MT-B. Algebraic hosts: the K_1/K_2 principle.**
- *Statement.* For every ring R ⊇ Q, St_N(R) is fp as soon as R is fp and N ≥ 5. With a Leavitt pair, one
  Steinberg group contains every GL_n(Q): St_4(R) does, and St_10(R_L) is the Problem 2.7 answer. But PE_N(R), R^x/Z(R^x), and every register or scalar completion are infinitely
  presented. The rational scalars Q^x (K_1) and the Tate symbols of K_2(Q) = Z/2 ⊕ ⊕_p Z/(p−1) survive as an
  infinitely generated central or elementary obstruction.
- *So:* algebraic hosts solve G′ and can never solve G. Any fp simple host must contain SL_n(Q) through something
  other than a ring's elementary group modulo its centre.
- *Inputs:* `rational-scalars-obstruct-fp-elementary-hosts`, `infinitely-generated-symbols-block-fp-elementary-groups`,
  `laurent-rational-symbols-block-fp-elementary-groups`, `matrix-corner-laurent-rings-block-fp-elementary-groups`,
  `leavitt-scalar-commutators-block-fp-central-quotients`, `ibn-failure-makes-rational-scalars-elementary`,
  `full-corners-must-kill-rational-k2-symbols`, `register-comparison-presentations-are-not-simple` (the two-register
  squeeze), `dilation-letters-cannot-divide-the-unit-class`, `bounded-harmonic-rings-are-not-finitely-presented`,
  `steinberg-groups-of-fp-rings-are-fp-in-rank-five`, `one-steinberg-group-contains-every-gl-n-q`.

**MT-C. Coherence.**
- *Statement.* Every finitely generated subgroup of GL_n(Q) embeds in one fixed family of fp simple groups
  (`fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups`). GL_n(Q) embeds in an ultraproduct of fp simple
  groups (`gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups`). And G holds exactly when the chain GL_n(Z[1/m!])
  embeds coherently (`ascending-unions-embed-along-coherent-chains`).
- *So:* no finitary invariant can obstruct G. That includes properties of finitely generated subgroups, torsion,
  single-element distortion, and FW of finitely generated pieces. An obstruction must be a *growth or coherence*
  invariant along the chain u(1/m!): nucleus depth, rewrite depth, register overflow, symbol growth.
  gq-deep-free-3's Needs line says the same.
- *Use.* Point every remaining obstruction lane at coherence invariants.

**Resulting host profile (n ≥ 3).** Every fp simple host S:
- has no residually finite subgroup between GL_n(Q) and S (O1; `sl-n-q-lies-in-finite-residual-of-every-overgroup`);
- has exponentially distorted cyclic subgroups (BS(1,2), O4);
- contains every SL_3(Z[1/m]), so S is not a-T-menable and not inside a group with Haagerup;
- has no proper semisimple CAT(0) action and no faithful action on a 1-manifold;
- is not of germ type with any landed class of local groups (MT-A);
- does not contain SL_n(Q) through a ring's PE_N (MT-B);
- contains SL_m(Q) in every finite-index subgroup and in its commutator cores
  (`sl-m-q-passes-to-finite-index-and-commutator-cores`).

## 4. Graph hygiene found in passing

- **Two different rings are both called `R_T`.** One is the Toeplitz ring with number operator in
  `q-embeds-in-a-corner-of-a-fp-toeplitz-ring` and `gl-n-q-embeds-in-e-n-plus-1-of-a-fp-ring`, which is fp. The
  other is the SL_3(Z) Toeplitz harmonic ring in `sl3-toeplitz-harmonic-*`, whose E_N is REFUTED as fp (1111ca113).
  Rename one; the collision reads as a contradiction.
- `gl-n-q-embeds-in-e-n-plus-1-of-a-fp-ring` is unreviewed but load-bearing for G′.
- The Problem 2.7 node rests on triple-refereed inputs. Its own "natural" clause is correctly left to experts; keep
  the Mikaelian announcement (arXiv:2507.04347 §1.4) in its priority context.
- The duplicate SL_2(Q) ids (`sl2-q-...`, `sl-2-q-...`) are reconciled by equivalence routes. That is fine.
