# Boone–Higman: master route (synthesis v2, 2026-09-18)

Lead synthesis of the 09-18 BH swarm (lane `bh-synth-lead`). v1 was 12a123bf1. v2 merges the
reductions (87daac9eb), obstructions (5f923fc28) and hosts (03663c211) syntheses. It is a
strategy document, not a proof; most cited nodes are unreviewed lane proofs whose status
lines govern. The live lane table is `board/SYNTHESIS.md`.

## 0. Thesis

Four independent synthesis lanes reach **one route and one missing theorem.**

- **The route:** `boone-higman-via-leavitt-units-of-rigid-sft-overgroups` (ring side), with
  its group-side twin `boone-higman-via-v-times-aperiodic-sft-full-groups`.
- **Why each lane lands there:**
  - **Reductions (canonical inputs).** Every universal host must contain the simple
    Kazhdan groups H_Γ = EL_3(R_Γ), where R_Γ is a Cantor crossed-product algebra
    (`decidable-host-classes-reduce-to-canonical-kazhdan-groups`). The master host,
    units of a Leavitt tensor of a Cantor crossed product, has exactly this shape.
  - **Obstructions (complexity wall).** Every finite-presentation certificate on main
    certifies *deterministic* local rules. Those cap the word problem and push a Kazhdan
    input into a unit or actor group, which is a recursion trap. A universal host needs
    finite presentation for *non-deterministic* finite-type dynamics: 2D SFTs and
    fixed-point tilings.
  - **Hosts (one machine).** B_A = (faithful coded action) + (fp of the Cuntz-stabilized
    full group). Unit groups of coded groupoids act residually finitely, and rank one is
    local. So simple Kazhdan inputs need rank ≥ 2, and the top missing engine is a
    finiteness theorem for **non-LCM** splitting categories.
  - **This lane (the local rigidity principle, LRP).** A host is fp only if its global
    structure is the unique solution of finitely many local rules. Every kill this week is
    a non-rigid model; every success is a rigid finite-type coding.

**The unifying statement.**
- *The missing theorem is:*
  > **(FTR) finite type + local rigidity ⇒ finite presentation, for non-deterministic
  > codings.**
- *Where FTR stands today:*
  - **Ring side, proved:** `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.
    This is the one non-deterministic certificate on main.
  - **Group side, open:** the P2′ gate below, and the hosts lane's "Li without lcms"
    (non-LCM means several refinements exist, i.e. non-determinism).
- *What's left for the route:* the rigid object itself. Over a finitely presented
  decidable envelope of each input, we need
  > **(★) a quantum-rigid free minimal SFT.**
- *Decidability* is consumed exactly at (★) (Jeandel: fp + strongly aperiodic SFT ⇒ decidable WP).

## 1. The local rigidity principle (LRP): the evidence

| Kind | Node | Mechanism |
|---|---|---|
| kill | `free-shift-houghton-like-envelopes-are-not-fp` | generic enumeration locally stable; far transplants invisible |
| kill | `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators` | fp ⇒ ν is the unique solution of finitely many local rules |
| kill | `fp-pl-groups-with-f-have-no-transcendental-support-endpoints` | relators see finitely many inequalities, so deform |
| kill | `fp-alternating-full-groups-of-free-subshifts-force-sft` | fp ⇒ finite type |
| kill | `v-times-golden-silver-wang-product-full-group-is-not-fp` | two independent faults translate apart |
| kill | `fp-v-times-subshift-full-groups-force-quantum-rigidity` | every operator model of the rules must commute |
| kill | `annular-free-product-germ-hosts-are-not-finitely-presented` | independent depths; no rule carries depth n to depth n+1 |
| kill | `eventually-periodic-genuine-shell-actions-give-fp-envelopes` | in 1D, rigid means periodic, so only virtually abelian inputs |
| success | `finitely-coded-cantor-actions-give-type-a-hosts` | Li's (UFP\*): unique factorization |
| success | `a2-lattices-embed-in-fp-simple-groups` | pencil closure in projective-plane links (local → global) |
| success | `cocompact-tree-product-lattices-lie-in-type-a-class` | cube k-graph, power and phase |
| success | `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` | ring side: rigidity suffices |

The LRP is the obstructions lane's (R) (fp-rigidity in marked groups); its (Z) is the group-side face.

**Design rules (for every lane).**
1. **Rank ≥ 2, one-ended.** Rigid N-codings are periodic. Houghton and shell routes are
   1D shadows. Rank-one hosts confine zero sets and put FW inputs in local groups (hosts:
   `rank-one-cone-hosts-put-fw-groups-in-local-map-groups`).
2. **Couple product factors.** Uncoupled factors give independent faults (golden–silver).
3. **Never rely on amenability of Λ.** Osajda inputs force non-exact Λ; invariant measures block
   compression, the known fp mechanism. Prefer Λ₀ × F₂.
4. **Complexity must sit in Λ, not in units.** Units act residually finitely
   (`finitely-coded-unit-groups-act-residually-finitely`), and finite units give an
   exponential cap.
5. **Kazhdan inputs enter by global Λ-inclusion,** i.e. hosts' slot (P). The
   canonical-input filter kills amenable, Haagerup, RF and finite-Kazhdan host classes.
6. **Central classes need free codings.** Boundary covers cannot untwist a class that
   survives on stabilizers. A free SFT carries all of Λ, centre included.
7. **Q-divisibility sits in Λ,** never in dynamical masses or the degree monoid.

## 2. Strategy 1, the master route

```
G decidable
 └ G0  Clapham: Λ₀ ⊇ G fp, solvable WP                         [supplied]
   └ G1  (P1) Λ = Λ₀ × H with a free minimal SFT X               [OPEN] = M2 + M1
     └ G2  X quantum rigid (large D, over F₂)                    [OPEN, THE CRUX]
       ├ ring: (E) B = LC(X,F₂) ⋊ Λ fp            (FTR ring side: established)
       │       └ G3r (K): K₁ = K₂ = 0 for B ⊗ L_{F₂}(1,2)      [OPEN; torsion-free FJ Λ done]
       │         └ A0 Khanh import ⇒ (B⊗L)^× fp simple ⊇ G      [conditional, cheap to discharge]
       └ group: G3g (P2′ = FTR group side): A(G_V × Λ⋉X) fp    [OPEN, unattempted]
                └ G4: simple + type (A) ⇒ PBH                    [supplied]
```

- **G0.**
  - *The input.* It may be simple Kazhdan, or the canonical H_Γ.
  - *For BBMZ 5.3(5).* Take Λ₀ = **St₁₀(R_L)**: fp, with solvable WP (refereed),
    containing every GL_n(Q). Over F₂ its central Q^× lies in the *acting group*, not in
    the ring's scalars, so the scalar obstruction does not arise (§8.1).
- **G1.**
  - *Supplied:*
    - the necessity results (Jeandel, Cohen);
    - `plane-constant-minimal-sft-factors-are-effective-minimal`;
    - the split into M2 (an effective minimal free subshift on Λ₀) and M1 (a group
      Durand–Romashchenko minimal simulation one Z² up);
    - paradoxical free minimal subshifts.
  - *Missing:* M2 for any non-abelian simple Kazhdan envelope; M1 beyond Z^d.
- **G2.**
  - *Supplied:*
    - rigidity ⇔ fp crossed product over Z², with sufficiency over every fp Λ;
    - wall rigidity ⇔ an idempotent commutator ideal;
    - Labbé's shift is wall-rigid;
    - permutive-triangle SFTs are rigid;
    - three kills: periodic quantum tilings, positive entropy, split faults.
  - *Missing:* **no quantum-rigid free minimal SFT is known over any group.**
  - *Tools:* Ã₂ pencil closure; the (UFP\*) analogy; Labbé's crossing faults;
    fixed-point parse uniqueness (§9).
- **G3r.**
  - *Supplied:* the gq Leavitt toolkit (one-step stabilization, refereed K₂ stability);
    Ara–Brustenga–Cortiñas with KH vanishing; the case of torsion-free Farrell–Jones Λ.
  - *Missing:* the NK-terms for non-regular B; Λ with torsion.
- **A0.** Read Khanh arXiv:2609.08428 at source. This discharges the conditional of the
  whole Leavitt route, and of bh-free-26's coNP^⊕P host.
- **G3g.**
  - *Idea:* a Stein–Farley complex on prefix-tree × pattern-cylinder partitions, where
    rigidity should make the "mergeable pattern" descending links highly connected.
  - *Why pair it:* it is the same theorem type as hosts' non-LCM gate (§8.3), so one lane
    should attack both.
  - *Payoff:* PBH.

## 3. Strategy 1b: coded groupoids (the hosts program)

- **The statement** (Li `thm:ZS` + `finitely-coded-cantor-actions-give-type-a-hosts`). A
  finite-object left-cancellative (UFP\*) category with (F), enough loops and F_n units
  gives type (A) automatically.
- **What fits already.** Hyperbolic groups, tree and Ã₂ lattices, CT_P(Z), RCWA groups and
  2V_τ.
- **The limit.** These categories are deterministic, and their units act residually
  finitely, so they reach structured classes, not the universal hard input.
- **The upgrade.** "Li without lcms" (dissection categories) is the group-side FTR.
- **The bridge.** Rigid SFT ⇒ non-LCM extension-move category. It would make P2′ follow
  from a non-LCM Li theorem.

## 4. Strategy 2: algebra BH in characteristic p

- **Route.** G ≤ F_p[G]^× ≤ A^× for an fp simple A with K₁ = K₂ = 0 for L ⊗ A. This is
  `decidable-group-algebras-have-fp-central-simple-hosts`.
- **Gates.** (A1) algebra BH, starting from the Bokut and Belyaev lineage at source.
  (A2) is G3r.
- **Relation to Strategy 1.** LC(X,F₂) ⋊ Λ is one such A.

## 5. Strategy 3 (backup): BH ⇔ PBH, and closures of B_A

- **The equivalence.** BH ⇔ PBH is BFFHZ Q3.4, or FFWZ Q5.9 after the FFWZ stabilizer gap
  is repaired.
- **The one known gap.** The only recorded fp simple group not known to be in B_A is the
  Titz Mite–Witzel kernel. Its MIF would close product closure and joint embedding for every
  recorded group.
- **The limit.** Closure theorems calibrate BH but cannot prove it (the reductions
  lane's collapse theorems).

## 6. Lanes

See `board/SYNTHESIS.md` for names and status. By gate:
- **G2** (6): labbe, permutive, f2f2, buildings, obstruct, and fixedpoint (proposed).
- **G1** (4): simulation, M2 ×2, rigid-simulation.
- **G3g + non-LCM** (2).
- **G3r** (1), **A0** (1), **S2** (1), **S3** (2: Titz Mite–Witzel MIF; FFWZ Q5.9), **verification** (2).

**Retire or re-scope** isolated test-group lanes (H4, BG, BS(2,3), Out(F_n) stabilizers,
Artin atoms, dendrites). Each becomes "a rigid finite-type coding over an fp overgroup?",
an instance of G1 ∧ G2.

**Structured-class lanes.** These use the hosts program and are not on the universal path:
- closed MCG (𝒯_m) and Deligne (2V_Λ): the non-LCM gate;
- higher-rank germ extensions: test PE_N(R_L), Deligne, Q_{g,2}.

## 7. Assessment: true or false?

**Leaning true, about 65/35.** The obstructions lane concurs: "the obstructions give no
evidence for falsity".

**For:**
1. Every obstruction is an LRP or (Z) instance aimed at one host family, not an invariant
   of all fp simple groups.
2. Separators must omit nested Kazhdan decidable hosts and cannot be Π₃ properties.
3. Jeandel's duality puts decidability exactly at the route's one consuming gate.
4. Four independent syntheses, and bh-writeup's pass (408c4dc50: "wrapper solved, the
   actor is everything", "fp is regularity"), converge on one route.

**Against:**
1. No quantum-rigid free minimal SFT is known over any group, and compression is blocked
   for amenable Λ.
2. Rigidity may not survive simulation, because reading pressure grows exponentially.
3. Three separator candidates survive: a uniform recursive WP bound, exactness, and
   coarse embeddability of all fp simple groups. The data cannot rule out the WP bound.

**Decisive objects:**
- *Toward true:* one quantum-rigid free minimal SFT over a one-ended group, a non-amenable
  one or a fixed-point tiling.
- *Toward false:* a rigidity obstruction for all free minimal SFTs over one-ended groups,
  or a uniform complexity bound.

## 8. Merged sibling syntheses: reconciliation

### 8.1 Reductions (87daac9eb)

**Canonical inputs** (`decidable-host-classes-reduce-to-canonical-kazhdan-groups`, proved).
For *every* class 𝒦, 𝒦 hosts all decidable groups iff it hosts every H_Γ = EL_3(R_Γ), where
R_Γ = LC(2^{C(Γ)},F₂) ⋊ (Z/2≀C(Γ)).
- *Reconciled.* This explains the master host's shape: H_Γ already lives in (R_Γ⊗L)^×.
- *Sharper form.* The route becomes a **Higman embedding theorem for Cantor crossed
  products**: replace the fg crossed product R_Γ by an fp one over a larger Λ. (E) is this
  statement. For BH it suffices that Γ ≤ Λ.

**Collapse theorems.** Closures reach all decidable groups only if their base does. So
closure lanes calibrate but cannot finish; this is Strategy 3's scope.

**Ranking "M2 first".** I adopt it as the execution order, with one correction.
- *The correction.* M1 + M2 give (P1) = G1 only, not (E). (E) needs G2: golden–silver is
  minimal, free and finite type, yet not rigid. No lane should build on (M1 ∧ M2 ⇒ E).
- *Reconciled ranking:*
  1. M2;
  2. in parallel, G2 on the Z² calibration;
  3. a rigidity-preserving M1;
  4. A0;
  5. K;
  6. P2′;
  7. closures.

**"GL_n(Q) via (E), not R_L".** Adopted as follows.
- *Dead:* the Steinberg-quotient route over R_L. Its central Q^× is not fg
  (`leavitt-scalar-commutators-block-fp-central-quotients`).
- *Surviving:* St₁₀(R_L) as the *acting group* Λ₀ of (E), where over F₂ the Q^× is a
  harmless central subgroup of Λ.
- *Consequence:* 5.3(5) = G1 ∧ G2 for Λ₀ = St₁₀(R_L), or for any fp decidable
  Λ₀ ⊇ GL_n(Q).

### 8.2 Obstructions (5f923fc28)

**(Z) zero-set confinement** (`zero-set-confinement-unifies-host-obstructions`, proved).
BS roots and FH/FW subgroups land in the zero set of every stable length. Rank-one hosts
confine the zero set; rank ≥ 2 hosts do not.
- *Reconciled:* design rule 1. Λ ⋉ X is rank ≥ 2 by construction.

**The complexity wall.**
- *Reconciled:* it is exactly why G2 is the crux. X *is* non-deterministic finite-type
  dynamics, and the ring-side FTR is the one certificate of that kind on main.
- *Their "decisive technical question"* (fp certificates for hierarchical tilings) is G2.

**Master candidate** (a DRS fixed-point tiling groupoid, programmed with the WP and
stabilized by O₂). This is the route with X chosen as a fixed-point tiling.

**The Q-exact diagnostic.**
- *Ring side:* it does not bind, since the host is a unit group.
- *Group side:* Λ ⋉ X is non-amenable whenever Λ is non-exact, as rule 3 requires.

### 8.3 Hosts (03663c211)

**One machine.** B_A = coded action + fp stabilized full group, with a Stein–Farley / Li
engine. This is Strategy 1b.

**Units act residually finitely** (`finitely-coded-unit-groups-act-residually-finitely`).
- *Reconciled:* this is rule 4, and it is why the route puts the input in Λ (slot P) and
  never in units.
- It also sharpens the complexity wall: in a coded groupoid, a hard input can only enter
  as piecewise elements.

**Rank one is local** (`rank-one-cone-hosts-put-fw-groups-in-local-map-groups`).
- *Reconciled:* rule 1. Hosts' master reduction (rank ≥ 2 coded action + fp) is the
  group-side form of the route, applied to finitely coded groupoids.

**Top gate: "Li without lcms"** (dissection categories; 𝒯_m for closed MCG, 2V_Λ for
Deligne). It is an instance of the group-side FTR, since non-LCM means non-deterministic.
- *Proposal:* one theorem-type lane on non-LCM Stein–Farley complexes, serving P2′,
  𝒯_m and 2V_Λ at once.

**Higher-rank germ extensions** (BHM over 2V). A structured route: it avoids rank-one
locality but not the complexity wall. Its test cases are PE_N(R_L), Deligne and Q_{g,2}.

## 9. New synthesis insight: fixed-point tilings supply the cross-depth rule

Three independent lessons ask for one ingredient:
- **bh-free-22:** fp needs "a finite rule transporting depth n to depth n+1".
- **Ã₂ pencil closure:** local structure propagates to global irreducibility.
- **(★):** rigidity must pass from windows to the whole plane.

A self-simulating (fixed-point) tiling has exactly this. Each level-k macro-tile is
determined by one finite rule applied to its level-(k−1) parse, with the same rule at every
level.

> **Conjecture (G2-fp).** A fixed-point tiling with locally unique parse is quantum rigid.

- **Proof strategy:** induction on levels. A commuting operator family on level-(k−1)
  supertiles extends uniquely to one on level-k supertiles; this is the operator version of
  unique parsing.
- **Over Z²:** it gives (★), the calibration gate T and `free-minimal-z2-sft-is-quantum-rigid`.
- **Over Λ₀ × Z²:** combined with a rigid simulation, it gives (E), hence BH, for every
  decidable input through the ring side.
- **Lane:** the proposed bh-g2-fixedpoint.
