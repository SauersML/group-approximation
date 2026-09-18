# gq critic pass 3 (2026-09-18): the remaining design space

Lane `gq-critic`.

**Inputs read.**
- `research/artifacts/gq-gq-obstructions-0918-writeup.md` (8c1393539);
- `frame-generated-simple-rings-have-no-vacuum`, `unit-symmetries-of-a-core-are-graded-or-inessential`,
  `isometric-shift-frames-over-uhf-bases-fail-the-k-budget` and `frame-unit-symbols-can-vanish-without-a-grading`;
- the T_p PARKED status (`central-deformation-euler-host-has-fng-steinberg-residual`);
- `prime-shift-group-k2-is-finitely-presented`, Attempts 3–4;
- the 69 lane boards, and every gq claim node on origin/main at 2af1a6a8e: 227 ESTABLISHED, 62 OPEN, 4 REFUTED.

**Conventions.** No claims of my own; node ids are backticked. Every question below is a question of this graph,
not a printed problem. The printed targets remain BBMZ arXiv:2306.16356v3, Problem 5.3(5) (the root
`gl-n-q-embeds-in-fp-simple-group`) and Problem 2.7.

## 1. Surviving construction shapes

Each shape lists the nodes that bound it and its single sharpest open question.

**S1. The ring route: PE_N(R) itself is the fp simple host.** It needs a ring R ⊇ Q such that E_N(R) is finitely
presented, PE_N(R) is simple, and the central quotient is finitely presented. `q-algebra-elementary-quotients-contain-gl-n-q`
then gives every GL_n(Q), and no type (A) action is needed.
- *Bounds:*
  - `rational-scalars-obstruct-fp-elementary-hosts` (applies when the rational scalars are elementary);
  - `ibn-failure-makes-rational-scalars-elementary` and `leavitt-tuples-make-rational-scalar-powers-elementary`
    (so IBN is needed);
  - `rational-k1-detection-forces-infinite-order-unit-class`;
  - `graded-rings-with-degree-one-units-fail-the-k-budget`, `isometric-shift-frames-over-uhf-bases-fail-the-k-budget`,
    `unit-symmetries-of-a-core-are-graded-or-inessential`, `frame-generated-simple-rings-have-no-vacuum`;
  - the register squeeze: `register-comparison-presentations-are-not-simple`,
    `single-register-rings-divide-unit-at-finitely-many-primes`, `top-determined-register-rings-cannot-divide-the-unit`,
    `dilation-letters-cannot-divide-the-unit-class`;
  - `bounded-harmonic-rings-are-not-finitely-presented`;
  - the Euler and resolvent symbol nodes (Part I.B of the writeup);
  - `infinitely-generated-symbols-block-fp-elementary-groups`.
- *Helpful:* `algebraic-closure-kills-rational-steinberg-symbols` and
  `torsion-k1-modulo-central-scalars-kills-scalar-symbols`. With Q̄ central and K_1(R) torsion modulo the central
  scalars, every scalar symbol {λ, x} dies.
- *Sharpest question:* the parked multi-type case, Attempt 10 of `fp-simple-resolvent-ring-with-divisible-unit-class`.
  For a base with K_0(B) ⊗ Q finite-dimensional, K_1 detection forces det(1 − φ_*) = 0. Are the resulting K_2
  classes in the image of K_2(N,R)? The Pimsner sequence it needs is now available for single-register completions
  (`register-completion-pimsner-from-supercoherence`). See also §2 item 6, which widens this shape.

**S2. Type (A) / B_A: prime-mixing actors.**
- *Bounds:*
  - `permutational-host-forms-agree-for-countable-inputs` (the target's forms);
  - `cocompact-fg-stabilizer-actions-force-finite-generation`;
  - `type-a-orbit-accumulation-forces-fg-nontrivial-germs`;
  - `rf-near-image-permutation-groups-omit-rationals`;
  - `fg-restricted-product-actions-have-finite-support` and `adelic-median-graph-automorphisms-are-restricted-products`
    (no coordinatewise host);
  - `sl-2-q-root-group-is-parabolic-in-every-prime-factor`;
  - `prime-shift-affine-group-a1-is-not-finitely-presented`, `prime-shift-kn-fp-reduces-to-a-metabelian-quotient`,
    and `torus-amalgams-of-adelic-groups-are-not-finitely-presented`. For every prime-permuting H, finite
    presentation is possible only through a hidden relation;
  - `unimodular-line-pairs-detect-cyclic-quotients` (line actions of E_N);
  - `steinberg-leavitt-resolvent-groups-have-no-type-a-action`, which is OPEN and conditional on
    `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`.
- *Sharpest question:* `prime-shift-group-k2-is-finitely-presented`. By Attempt 3, e ∈ N holds if and only if one
  explicit three-line fixer r lies in N. Attempt 4's bounded search found no hidden relation. Also still needed:
  `prime-shift-affine-group-a1-has-fg-point-stabilizer` (for type (A)) and `prime-shift-hnn-map-to-a1-is-injective`.

**S3. Brin–Thompson: plain nV, or twisted SV_Γ.**
- *Bounds:*
  - `rational-stepping-stones-in-nv-need-bs12-or-heisenberg`;
  - `nv-rational-subgroups-with-power-conjugacy-are-flat` and `scaled-rationals-in-nv-need-aperiodic-core-elements`;
  - `bs12-images-in-nv-have-logarithmic-table-length`;
  - `renormalization-return-times-tend-to-zero-adically`;
  - `crossing-move-hierarchies-have-odd-branching` (a method bound; see §2 item 3);
  - for n ≥ 3, route `kazhdan-finiteness-in-nv-via-cnd-transversal`, conditional on
    `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`, which has no status line.
- *Twisted SV_Γ.* `fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups` handles every finitely generated
  piece. For the whole group, SV_Γ reduces to S2.
- *Sharpest question:* `bs12-embeds-in-brin-thompson-2v`. Within reach is its test case: does the +4 return
  offset of U° hold at all radii? It is certified to radius 18. By `renormalization-return-times-tend-to-zero-adically`
  item 3, that would exclude a height-2 renormalization of the leading candidate. It would not decide the node.

**S4. Self-similar and one-prime-left-out (Z_(ℓ)) routes.**
- *Bounds:*
  - the bottleneck `z-localized-embeds-in-fp-rf-group`, with the class exclusions of writeup Part I.A;
  - `resolvent-elementary-groups-are-not-fp`;
  - `resolvent-steinberg-rf-residual-is-infinitely-normally-generated`;
  - `euler-ring-rational-symbols-are-infinitely-generated`;
  - `euler-triangular-steinberg-retracts-to-euler-steinberg` and `one-sided-inverses-cannot-repair-the-steinberg-residual`;
  - `finite-state-mobius-pieces-see-finitely-many-primes` and `p-adic-dilation-normalizers-act-by-power-maps`;
  - `iwahori-overgroups-not-automaton-linear-or-metabelian` and `aperiodic-tree-almost-automorphism-fg-subgroups-are-rf`.
- *T_p is PARKED* with three stated needs: I_rf(B) finitely generated, K_2(B, B_+) detection, and unstable K_2.
- *Sharpest question:* the open finite-quotient cases of `euler-ring-steinberg-rf-residual-is-fng`, namely K_2 of
  F_(r,N) with r ≥ max(l,3). At r = l the expected survivor is u^(l−1) du.
  - If every c_q dies in every finite quotient, the residual carries the Euler symbols and the T_l route closes.
  - A survivor keeps the route alive.

**S5. Germ-type hosts with wild local groups.** `germ-type-hosts-of-gl-n-q-fail-in-landed-local-classes` (MT-A) and
`gl-n-q-almost-v-hosts-need-lattice-germs` leave exactly one kind of germ-type host: one whose germ group is itself a
group of the required kind.
- *Sharpest question (untested; §4 U2):* can a finite germ extension of V realize a quotient of an fp group
  containing GL_n(Q), such as St_N(R_L), as a singular germ group while its local stabilizers S(M,M′) stay finitely
  presented? The latter is the hypothesis of Belk–Hyde–Matucci arXiv:2407.03149, Theorem 2.1.

**S6. The rational group R, Aut(V), and RSGs.**
- *Known:* `pgl-2-q-embeds-in-the-rational-group` (2 referees). But R is not finitely generated, and
  `rsg-equicontinuity-program-cannot-exclude-gl-n-q` shows the equicontinuity program cannot exclude it.
- *Sharpest question:* `aff-q-embeds-in-aut-v`. By its item 1 this is equivalent to Aff(Q) ≤ Out(V) ≅ O_2, and the
  first test is whether O_2 has infinitely divisible elements (gq-deep-free-3, Needs (ii)).

**S7. Literature constructions nobody has tested.** See §4 U3–U4.

## 2. Exclusions that may be too strong

1. **My pass 2, family 1: "the adelic complex has one vertex orbit, i.e. it is cocompact".** This is wrong. The
   quotient has one vertex per squarefree integer and infinitely many edge orbits
   (`cocompact-fg-stabilizer-actions-force-finite-generation`, item 3, as recorded in
   `sl2-q-in-permutational-boone-higman-class`). No cocompact model with finitely generated stabilizers exists
   (item 2).
2. **My pass 2, MT-B: "ring hosts can never solve G" is too strong.** The landed
   `ring-hosts-of-gl-n-q-meet-the-k1-k2-principle` states its heuristic reading as not claimed. Its quotient
   obstruction needs elementary rational scalars (`rational-scalars-obstruct-fp-elementary-hosts`). St_N(R_L) as a
   subgroup of some fp simple group is not excluded at all. It is excluded only as a type (A) actor, and only
   conditionally (`steinberg-leavitt-resolvent-groups-have-no-type-a-action`).
3. **"nV with BS(1,2) blocked by odd branching (4eb6fec15)" overreads a method bound.**
   `crossing-move-hierarchies-have-odd-branching` (lane proof) assumes one-head move hierarchies with bounded
   junctions and slowly growing domains, and concludes that binary hierarchies need return moves.
   `bs12-embeds-in-brin-thompson-2v` stays OPEN.
4. **gq-sl2q's board line "BLIW-type permanence: dead" needs a scope.**
   - It is right for actions of SL_2(Q) itself and for the schema (P) over ∏′T_p
     (`cocompact-fg-stabilizer-actions-force-finite-generation`, item 2).
   - It does not touch BLIW applied to a finitely presented **overgroup**, i.e. route `sl-2-q-via-hecke-overgroup-and-bliw`.
     That route is gated by `sl-2-z-localized-has-fp-hecke-overgroup`, and so by the S4 bottleneck.
5. **`unit-symmetries-of-a-core-are-graded-or-inessential`: the Scope line may be stronger than the proof.**
   - The Scope line calls closed "designs that get finite presentation from a unit shift". Item 4 says the same.
   - Items 3(b)–(d) prove less: finite generation of A, and a finite-order action of σ on K_0(A). Finite
     presentation of R is not shown to force finite presentation of A.
   - It is a lane proof. A referee should decide whether "finitely presented" there should read "finitely
     generated, with finitely many K_0 classes per σ-orbit".
6. **Conditions 1 and 3 of `fp-simple-resolvent-ring-with-divisible-unit-class` are design choices, not
   consequences of the root.**
   - The node calls itself "the coordinator's design target". Its necessary shape ("stateless, not stably finite")
     follows from condition 1, the resolvent vacuum, via `resolvent-vacuum-rings-have-no-k0-state`.
   - Condition 3, R ≅ M_n(R_n) for all n, matches the hypothesis of `matricial-divisibility-kills-rational-k2-symbols`,
     i.e. it kills K_2(Q). By `algebraic-closure-kills-rational-steinberg-symbols`, items 1–3, Q̄ ⊆ R unitally
     already does that.
   - So stably finite IBN designs with Q̄ ⊆ R are outside the gate but not outside S1. Among nodes seen, they are
     bounded only by `bounded-harmonic-rings-are-not-finitely-presented`, `af-groupoid-rings-have-no-fg-subring-containing-q`,
     the integral-form nodes, and the open `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`.
7. **Scoped correctly, no overreach found:**
   - `adelic-median-graph-automorphisms-are-restricted-products`: item 3 covers every abstract copy through the
     profinite K_S.
   - `prime-shift-affine-group-a1-is-not-finitely-presented`: fails "in its stated form" only. A_1 may still embed
     in an fp actor.
   - `p-adic-dilation-normalizers-act-by-power-maps`: germs at 0; a single relation is not excluded.
   - `finite-state-mobius-pieces-see-finitely-many-primes`: finite-state generators only.
   - `proper-semisimple-cat0-groups-contain-no-gl-2-q`: finitely generated, proper, semisimple.
   - `sl-n-q-lacks-property-fw`.
   - `torsion-k1-modulo-central-scalars-kills-scalar-symbols`: its K_2(Q̄) = 0 is correct, since K_2(Q̄) is torsion
     as a colimit over number fields and torsion-free by Bass–Tate.
8. **Graph hygiene.**
   - `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` and `some-gl-n-z-embeds-in-no-brin-thompson-group`
     have no bold status line. Root Attempt 11 correctly says "would kill".
   - "centre" in `prime-shift-kn-fp-reduces-to-a-metabelian-quotient` and elsewhere should be "center".

## 3. Ranking: P(decisive answer in a lane's reach) × impact on the root

1. **The S1 multi-type question, with §2 item 6 widening the gate to Q̄ ⊆ R.** A positive answer is the only shape
   that gives the root for all n at once, with no actor. The question is a concrete K_1/K_2 computation over one
   Pimsner sequence that is now available for single-register completions, so a no is plausible within one lane.
2. **`prime-shift-group-k2-is-finitely-presented`, via membership of the three-line fixer r.** This is a single
   membership question in an explicit group modulo an abelian quotient, next to the only explicit 2-transitive actor
   containing GL_2(Q). Either answer decides whether that actor family is live for GL_2(Q) in `B_A`, though the
   point-stabilizer question remains.
3. **The open F_(r,N) cases of `euler-ring-steinberg-rf-residual-is-fng`.** This is a finite ring computation, so it
   is in reach and likely decisive. If every c_q dies in every finite quotient, the T_l route to the S4 bottleneck
   closes. Its impact is limited to the n = 2 and Z_(ℓ) stepping-stone routes.

## 4. Natural ideas no lane has tried, and why they are not excluded

- **U1: stably finite IBN rings with Q̄ ⊆ R unitally,** as candidates for S1. They are excluded only by the gate's
  design conditions (§2 item 6), not by a node. The landed stably finite obstructions cover only harmonic crossed
  products, AF groupoid rings and integral forms.
- **U2: germ implant (S5).**
  - *The idea:* a finite germ extension of V whose germ group at one point is a quotient of an fp group containing
    GL_n(Q). Finite presentation of the host needs only finitely presented local stabilizers (BHM Thm 2.1), not a
    finitely presented germ group. So the infinitely many K_2 or scalar relations of E_N(R_L) might sit in the
    locally trivial part.
  - *Why it's open:* MT-A excludes only the landed local classes, and St_N(R_L) and its quotients are in none of
    them. `gl-n-q-almost-v-hosts-need-lattice-germs` asks for exactly such a germ group.
- **U3: Katsura–Exel–Pardo self-similar graph groupoids** and their topological full or Nekrashevych groups. The
  gq nodes mention Katsura nowhere. These give BS(1,m)-type isotropy from multiplier matrices, but only through
  wild copies: `germ-extensions-omit-standard-gl-n-q` kills the standard affine ones. They are not excluded, because
  their bisections need not be piecewise in one finitely generated affine or projective base.
- **U4 (lower value): symbolic-dynamics groups beyond Aut(σ).**
  - Aut of a full shift is residually finite (Boyle–Lind–Rudolph), so O1 kills it.
  - The mapping class group of a full shift (Boyle–Chuysurichay) and the stabilized automorphism group
    (Hartman–Kra–Schmieding) are not covered by that argument. Whether they are finitely generated or presented, or
    contain (Q,+), was not checked here.
