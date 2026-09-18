# Boone–Higman: master route (synthesis v5, 2026-09-18)

Lead synthesis of the 09-18 BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62, v4 fa0efca1c.
- **What v5 folds in:** every landing and LESSONS.md entry between v4 and the 14:22 recovery
  landings (§8).
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane
  proofs, and their status lines govern. The live table is `board/SYNTHESIS.md`.

## 0. Thesis (v5): rigidity is cheap, programmability is the crux

**Still standing from v1–v4:**
- **LRP:** finite presentation means the global structure is the unique solution of finitely
  many local rules.
- **FTR:** finite type plus rigidity gives finite presentation. Proved on the ring side.
- **Carrier principle (v4):** the input's complexity and coarse geometry are carried by the
  acting group Λ.

**New in v5: three facts that move the crux.**

1. **Freeness was never needed** (`master-route-needs-only-topological-freeness`, 04ce18852).
   - Both master routes use freeness only as topological freeness (effectiveness), plus torsion-free
     isotropy for the K-gate.
   - E1 and E2 therefore merge into one object:
     **(★′)** a quantum-rigid, minimal, topologically free SFT with torsion-free isotropy over a
     finitely presented overgroup Λ₀ of the input.
   - Decidability is consumed exactly here (`rigid-topologically-free-sfts-force-solvable-word-problem`).
2. **Rigidity is no longer scarce over non-amenable groups.** There are three independent
   mechanisms, and two of them are new since v4.
   - *Compression* (201fb24d4). The end shift of F_n is rigid at every scale over every field,
     with no determinism, by monotone chains of projections. Its square ∂T_m ⊠ ∂T_n is a rigid,
     minimal, topologically free SFT over F_m × F_n, so (★′) holds for every fg subgroup of
     F_m × F_n.
   - *Finite presentation is a rigidity certificate* (9b3fdd027). The necessity theorem holds for
     topologically free actions (`topologically-free-subshift-full-groups-force-quantum-rigidity`).
     Every finitely presented V-stabilized boundary host therefore certifies rigidity. That gives
     rigid, minimal, topologically free SFTs over every cocompact Ã₂ lattice, which is one-ended
     and Kazhdan.
   - *Determinism* (Z², v1–v4). It is the only mechanism with programmable language, and the
     only one still open (§2, gate 3).
3. **Hard inputs cannot act through geometry.** They must *scale* or *sit at an emitter*.
   - A group with (FA) and no finite quotients acts trivially on every locally finite tree and
     every Bruhat–Tits building (813bff6dd). That includes every simple Kazhdan input H_Γ.
   - In finitely coded groupoids, scaling-free inputs are residually finite (bh-groupoid, v4).
   - So a hard input either scales without bound along orbits, like a lattice on its boundary,
     or is a point stabilizer at a point with infinitely many local branches: an
     *infinite emitter*, i.e. a parabolic point.
   - Stabilizer engines (5fb3cdaea) realize the second option literally: the input S is the
     full isotropy of a vertex point of Z/2 ∗ S on its compactified Bass–Serre tree.

**Consequence: the crux moved from rigidity to programmability.** The v5 bottleneck is one design
problem, which I call **(IE)**, the infinite-emitter gate:

> Build a finite-type (finitely presented) coding of a compression-type boundary action in which
> an arbitrary decidable input sits at an infinite emitter.

Two routes meet at (IE):
- **Track A′.** The bh-g3-topfree node names the obstacle to (★′) over Λ₀ = Λ₁ ∗ Z (Clapham
  Λ₁ ⊇ G): "a Bass–Serre end orientation over a group with infinite vertex stabilizers is not a
  local rule over the group". Compression gives rigidity; the input vertex is an infinite emitter.
- **Track C (new: stabilizer engines).**
  - The route: BH ⇐ D(F_S) is finitely presented for every fg decidable simple S.
  - Li's Garside theorem fails there for the same reason: every vertex is an infinite emitter.
  - Necessity is proved: a finitely presented engine forces a decidable vertex group.
  - First test: Reid's group, B = Z (MathOverflow 339541).

**Conditional theorem v5.** BH ⇐ (★′) ∧ (K′) ∧ Khanh, where (K′) is Farrell–Jones with
coefficients for Λ₀ acting with torsion-free isotropy.
- It runs through `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`.
- **No P2′ is needed on the ring route.** P2′ is needed only on the group route (§2, gate 4).

## 1. LRP evidence (v5 additions marked +)

| Kind | Node | Mechanism |
|---|---|---|
| kill | `fp-alternating-full-groups-of-free-subshifts-force-sft` | fp ⇒ finite type |
| kill | `thick-building-flat-sfts-are-never-quantum-rigid` | a half-apartment lies in two apartments |
| kill | `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid` | wall certificate |
| kill + | `schur-multiplier-obstruction-kills-thickening-hosts` | H₂ of the fibre survives over FP₃ Λ |
| kill + | `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is` | folds import the fibre's rigidity problem unchanged |
| kill + | `triangle-permutive-sfts-have-one-sided-total-faults` | seedless determinism needs 3 semi-expansive directions |
| kill + | `local-lemma-cannot-certify-multiscale-recurrence` | recurrence is anti-local |
| success + | `free-group-boundary-shifts-are-quantum-rigid` | compression: monotone projection chains |
| success + | `a2-lattice-boundary-skew-shifts-are-quantum-rigid` | fp host ⇒ rigid boundary subshift |
| success + | `topologically-free-subshift-full-groups-force-quantum-rigidity` | necessity needs one free point per cylinder |
| success + | `boolean-inverse-monoid-finite-presentation-is-finite-type` | idempotents commute by axiom; all difficulty is the units functor |
| success + | `v-cone-sliding-localizes-disjoint-support-relations` | disjoint-support relations have bounded diameter |
| ~~success +~~ refuted | `perron-substitution-finiteness-for-garside-full-groups` | proof invalid (ba9176b48a): Li needs merge packing, not a Perron height; `cuntz-stabilized-garside-full-groups-are-f-infinity` (16be960ff1) gets packing from the Cuntz colour |
| success | `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale` | scale collapse |
| success | `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` | ring FTR |

**Reading.** Every new kill localizes a failure to one layer: fibre, multiplier, recurrence or
one-sided faults. Every new success is a *transfer*, of rigidity along compression, of
finiteness along fp hosts, or of relations along cones. Nothing kills programmability.

## 2. The gates (v5)

```
(IE) infinite-emitter finiteness  ── feeds ──┬─ Track A′: (★′) over Λ₀ ⊇ G by a compression coding
                                             └─ Track C: D(F_S) fp for decidable simple S ⊇ G
(★′) rigid minimal topologically free SFT, torsion-free isotropy, over fp Λ₀ ⊇ G
 ├ route 1 (ring):  (★′) ∧ (K′: FJ for Λ₀) ∧ Khanh ⇒ BH            [no P2′]
 └ route 2 (group): (★′) ∧ P2′b (dynamics-free exactness) ⇒ BH     [P2′a is rigidity]
```

**Gate 1, (IE), infinite-emitter finiteness: the sharpest open gate.**
- *Its first instance is Reid's group* F_Z = [[(Z/2 ∗ Z) ⋉ X]] (b5ce5bff2). Is it finitely
  presented?
  - bh-free-56 recodes it as the Γ_θ hybrid of Thompson's T (parabolic germs) and V (Cantor
    cuts), and proposes Brown's criterion on a Stein–Farley complex of cut-edge partitions.
  - The known part: abelianization Z ⊕ Z/2, homology Z, Z, 0, …, and a simple fg commutator
    subgroup.
- *Why it is decisive.*
  - A positive proof is the first finiteness theorem at an infinite emitter. It is the template
    for D(F_S), where the proof must consume WP(S) (`fp-stabilizer-engines-need-decidable-vertex-groups`),
    and for compression codings over Λ₁ ∗ Z.
  - A negative answer kills the whole engine family and forces Track A′ to put the input
    somewhere other than an emitter.
- *Constraints any proof must meet.*
  - Homology cannot decide it: an unsolvable-WP perfect B gives a non-fp D(F_B) with the same
    isotropy homology (bh-free-60).
  - The vertex group's own finite presentation is not the right hypothesis. Decidability is.
- *K-gate warning.* Putting the input in isotropy is fine on the group route, but on the ring
  route (K′) needs torsion-free isotropy (trace detector). So parabolic designs carry
  torsion-free inputs, or they use route 2.

**Gate 2, (★′) over a Clapham square: the v4 route with freeness relaxed.**
- *Existence.* M2 plus BSS minimal self-simulation on Λ₁ × Λ₁.
  - (M2) is free for every effectively residually finite group, via Toeplitz subshifts from
    normal chains (cc32b1908).
  - For A ∗ Z, (M2) needs only one computable hyperaperiodic point universal at the origin
    (bh-g1-universal-point).
  - The wall is central→global recurrence, and it is real: Medvedev degrees (84c5e8d9a).
- *Rigidity.* The only open part is rigidity over the amenable fibre (gate 3), unless the
  existence proof itself produces a compression coding.
- *Calibration.* F_m × F_n is done; Ã₂ lattices are done.

**Gate 3, Z² rigidity with faults: rigidity where determinism fails.**
- *The fold lemma* (cc93f9797) merges v4's tests E2.1 and E2.2. ABHT's F_n × Z shift is rigid
  only if its Z² fibre is. The converse needs only the centrality condition (C) on a commuting
  skeleton (bh-g2-abh).
- *Where the difficulty is.* Labbé's shift has four fault directions, so no determinism proof
  in any recoding certifies J_D = 0 (264bcfe50). A proof needs a fault-crossing mechanism at
  resonant pairs.
- *What makes it finite.* Scale collapse turns it into a check at scale ≤ 5 (≤ 3 for DRS), which
  the bounded MSI search in bh-g2-fixedpoint-a is testing.
- *Why it still matters after (★′).*
  - Only determinism gives programmable language (DRS fixed-point tiles).
  - Track B needs a rigid Z² SFT with a row factor onto an arbitrary effective Y (ec7acf590).
  - Renormalization cannot dodge it: fp of a renormalized host would prove Labbé rigidity
    (bh-invent-03 §5).

**Gate 4, P2′ (route 2 only) now splits into two layers** (0326d0d8a, 3f547b04c, e4a7fb613).
- *P2′a, finiteness.* V-cone sliding reduces all disjoint-support relations to bounded diameter.
  What remains is commutation of conditioned copies at distance, which is quantum rigidity. So
  P2′a is supplied by (★′).
- *P2′b, exactness.* A dynamics-free, Coxeter-type local transposition presentation
  (`v-times-full-groups-have-local-transposition-presentations`). Attack it like Quick's proof
  for nV.
  - A homological shortcut is excluded: the gluing kernel is relatively perfect.
  - Since no subshift enters, this is a purely combinatorial theorem.
- *Monoid level.* The Boolean inverse monoid is fp iff it is of finite type (4c74c3eff). So all
  of P2′b's difficulty is the units functor.

## 3. Track B (fixed FJ scaffold, input in units)

- **Gate U** for simple inputs is exactly a coarsely dense, injective, Lipschitz realization of a
  Schreier quotient in the scaffold (52bfd4df9).
  - Kazhdan inputs kill amenable, polynomial-growth and virtually free scaffolds.
  - F₂ × F₂ passes every known test. Its sharp open case is
    `infinite-kazhdan-group-in-wobbling-group-of-product-of-trees`.
- **One-dimensional core**: the oracle Kirchberg embedding
  `decidable-algebras-embed-in-oracle-leavitt-crossed-products`. It is OPEN in general and solved
  for monomial algebras (1f6f43c20).
  - Amenable crossed products host only linear-sofic groups (a60ee46ee).
  - So the non-sofic input must come from language-conditioned Leavitt isometries.
- **Rank.** Below Tracks A′ and C. It needs gate 3 (a programmable rigid Z² SFT) in any case.

## 4. Strategy 3 and Q3.4 (BH ⇔ PBH)

- **Recorded groups.** Every recorded fp simple group is in B_A except W, W_(P,ℓ), and the
  projective Leavitt quotients at odd p.
  - (L_p ⊗ L_p)^× is in B_A for every prime p (c45c84429, conditional on Khanh). On the ring
    side PBH comes free once finite presentation is known; only the scalars block the odd-p
    quotients.
  - Every host machine on main squares itself (b043f3be1), so (SQ) is never a separate gate.
- **Q3.4 is now a kernel-removal question.**
  - Relative automorphisms act faithfully on free-product Hom-orbits (37da692b8). The kernel is
    therefore never the obstruction; the residue is the double-coset clause, which needs a
    Cantor scaffold.
  - Amalgams of orbit-finite actions along a common port are type [A₂] (a8f37a022). So relative
    PBH is local, and PBH is exactly "the free kernel is finitely normally generated", which is
    FFWZ Question 5.9.
  - A general kernel-removal theorem would turn every regular port into a PBH constructor.
- **Operadic actors** (b50f07270) are a strict generalization of type (A). Thumann's engine
  needs only F_∞ transformations. Finitely generated operads split over a label kernel, so the
  oligomorphic-operad conjecture is the programmable version.

## 5. Structured classes (MAJOR teams): each is now one named lemma

- **Closed MCG (5.3(2)).** BH for Mod(S_g), g ≥ 3, reduces to two statements about the
  edge-split operad in rank 6g − 6: Ore's condition and a finite spine (ef7fa0a1e).
  - Ore's condition is reduced further to one rearrangement lemma.
  - Type (A) holds without fullness: an Ore operad group containing GL_n(Z) contains the whole
    derived full group (`ore-operad-groups-contain-the-derived-full-group`).
  - Synchronization is proved off totally irrational rays (1a5d65604). The Stein–Farley gate is a
    Diophantine shared-vertex problem at totally irrational directions.
  - Lanes: bh-free-54, bh-free-61, bh-major-mcg-2.
- **Cubulated (5.3(10), Q1.15).** The Garside layer is free for every free cocompact
  cubulation, special or not (d172582dd).
  - What is missing is a power operation when time is a poset.
  - ~~The Perron criterion (4e48d1730) says a power is not needed, only a primitive
    type-substitution matrix with Perron value > 1.~~ Refuted (ba9176b48a). Li's proof needs
    merge packing, which fails along thin cycles (63bf7063b). Cuntz stabilization supplies it
    for every Li-Garside category with trivial units and (Acyc)
    (`cuntz-stabilized-garside-full-groups-are-f-infinity`, 16be960ff).
  - The finiteness gate is closed after stabilization. Q1.15 reduces to dynamical gates G1–G3:
    a closed bisection set, (Acyc), and comparison or minimality (Attempt 7 of the Q1.15 node).
  - Lanes: bh-major-cube-b, bh-invent-perron.
- **One-relator / H4 / BG (5.3(9)).** BS chains are towers of coordinate changes at one rational
  point, and they close up in germ extensions of V (98efce84c).
  - Cycles (H4, BG) need non-tame, zero-entropy, renormalizable elements.
  - Compiler drift forbids stacking compiled letters (c6bb38b91). So the needed machine is one
    whose renormalization map is itself renormalizable.
  - Every attempt lands on finite presentation of one germ group, via BHM's SingFix condition.
  - Lanes: bh-major-onerel, bh-one-relator.
- **Solvable.** Hall's non-RF quotient avoids V, circle groups and periodic ends
  (e14c8d77a).
  - The host needs odometer divisibility with aperiodic end cocycles.
  - The next step is Abels' A_p/C as the germ group. Lane bh-solvable.
- **GL_n(Q) (5.3(5)).** GL_n(Q) ≤ St₁₀(R_L), which is fp and decidable (1637708b6). So 5.3(5) is
  one instance of (★′), over an fp overgroup of St₁₀(R_L).
  - A Leavitt unit commuting with a Leavitt copy is exactly a self-doubling unit (4e5b8c074).
  - The finite-field Leavitt route is therefore one question: does an invariant-free unit exist?
  - P_Z rules out rank-one cone hosts, since St_N(R_L) has Kazhdan subgroups whose centre is
    not residually detected.
  - Lanes: bh-gln-centralizer, bh-free-16.
- **Out(F_n), branch hosts.**
  - Branch hosts are annular over V. Pinning is definability (ba298cb26), so natural drivers
    pin only bounded or ascending passengers.
  - Out(F_n) stays on Track A′.

## 6. Separators (what BH must pass)

- P_Z and P_eff (ac47d9909) are hereditary separator candidates. Each has a decidable
  witness outside it: Deligne's lattice or St_N(R_L) for P_Z, Rauzy's L(A) for P_eff.
- BH implies the separating side of each. For P_eff that is
  `fp-simple-group-containing-a-non-efrf-residually-finite-group`, which reduces to realizing one
  centralizer C_L(m) = U_A inside a B_A group.
- (RT), "f.g. torsion subgroups of fp simple groups are residually finite", is the uniform Burnside separator, with witness B(2,665). It is proved on synchronous and low-dimensional CAT(0) host families, and open on nV, asynchronous RSGs, type (A) actors and SFT full groups (`fp-simple-groups-have-residually-finite-torsion`).
- The separating sides are open construction problems implied by BH. None is a counterexample candidate with evidence.

## 7. Gate ranking v5 (decisiveness × tractability)

| Rank | Gate | Lanes |
|---|---|---|
| 1 | **(IE) at Reid's group:** is [[(Z/2 ∗ Z) ⋉ X]] fp? (Brown on cut-edge partitions; T/V hybrid) | bh-free-56, bh-free-60 |
| 2 | **(IE) general:** a finite-type compression coding with the input at an emitter; D(F_S) for decidable simple S | bh-free-60, bh-g3-topfree, bh-invent-* |
| 3 | **Z² rigidity with faults:** a fault-crossing mechanism for Labbé/DRS; scale-≤5 certificate (MSI); centrality (C) for the fold converse | bh-g2-fixedpoint-a, bh-g2-abh, bh-free-35 |
| 4 | **(★′) existence over Clapham squares:** MSS; M2 via one universal point for A ∗ Z | bh-g1-bss, bh-g1-universal-point |
| 5 | **P2′b:** Quick-type exactness of the local transposition presentation (group route only) | bh-one-relator, bh-free-09, bh-g3-tfc |
| 6 | **Q3.4 via kernel removal** (FFWZ Q5.9), with amalgam ports | bh-invent-02, bh-typeA-universal |
| 7 | **Gate U over F₂ × F₂;** oracle Kirchberg embedding | bh-algebra, bh-near-actions |
| 8 | **(K′):** FJ with coefficients for the chosen Λ₀ (conjectured for all groups) | — |
| — | Structured lemmas (§5): Ore rearrangement, Perron on cubes, renormalizable renormalization, Abels germ group, invariant-free Leavitt unit | MAJOR teams |

**Retired in v5:**
- **Freeness as a requirement.** Topological freeness plus torsion-free isotropy suffice.
- **v4's test E2.1 as an independent shortcut.** By the fold lemma, F_n × Z is the Z² fibre gate
  plus (C).
- **Flat (translation-lattice) building codings for rigidity** (bh-g2-buildings).
- **Seedless permutive rigidity** without three semi-expansive directions.
- **Telescopes as embedding engines.** They are finiteness engines only; infinite seeds leave
  every contracting host.
- **Thickening hosts over FP₃ groups** (Schur multiplier).
- **Tree and Bruhat–Tits geometry acting nontrivially on Kazhdan simple inputs.**
- **Full groups over subexponential-growth acting groups for Kazhdan inputs.**
- **The naive finite-centre separator** (integral Jacobi group).

## 8. Reconciliation log (v5)

- **Route-changing:**
  - 04ce18852 (topological freeness);
  - 201fb24d4 and 9b3fdd027 (compression; fp certifies rigidity; Ã₂);
  - cc93f9797 (fold lemma);
  - 5fb3cdaea and b5ce5bff2 (stabilizer engines, Reid);
  - 813bff6dd (Kazhdan filter);
  - 0326d0d8a, 3f547b04c and e4a7fb613 (P2′ layers);
  - 4c74c3eff (BIM).
- **Track B:** 52bfd4df9, 1f6f43c20, ec7acf590, a60ee46ee, c26b805aa.
- **S3 / Q3.4:** 37da692b8, a8f37a022, c45c84429, b043f3be1, b50f07270.
- **Structured classes:**
  - ef7fa0a1e, a6eee828f, 1a5d65604 (MCG);
  - d172582dd, 4e48d1730 (cubes);
  - 98efce84c, c6bb38b91, 8c815a108, ed0651eb7 (one-relator, germ hosts);
  - e14c8d77a (Hall);
  - 4e5b8c074, 1637708b6 (GL_n(Q));
  - ba298cb26, 264d89930 (branch, self-similar).
- **Obstructions and tools:**
  - aa0ae6e48 (Schur), ec8c1c33b (permutive), b81707e5f (recurrence);
  - cc32b1908, 84c5e8d9a (M2);
  - 264bcfe50 (fault slabs), 043451803 (finite seeds);
  - ac47d9909 (separators).
- **Off-route named results**, recorded but not route-changing:
  - Kourovka 21.73 and the 21.74(a) obstruction (a95cb1edf, 7c6468c08);
  - MZ Question 3.18, reduced to Σ¹-symmetry (f2802a9da);
  - the BS(1,2) binary hierarchy design (7abe7ced6).

## 9. Assessment

**BH true: leaning yes, about 65/35.** The number is unchanged, but the risk has moved.
- **For:**
  - Rigidity, the v4 crux, is supplied over non-amenable groups by two mechanisms that need
    nothing from the input: compression, and fp-certification.
  - The ring route needs no P2′.
  - Every recorded fp simple group is in B_A, except W, W_(P,ℓ) and the odd-p Leavitt quotients.
  - No separator has a witness pointing to a counterexample.
- **Against:**
  - Every hard input must sit at an infinite emitter or scale without bound, and no finiteness
    theorem at an infinite emitter is known, not even for B = Z.
  - Programmable rigidity (Z² with faults) is still open, and no rigid SFT with programmable
    language is known over any group.
- **The single most informative next proof:** decide finite presentation of Reid's group
  [[(Z/2 ∗ Z) ⋉ X]].
  - A proof is the first finiteness theorem at an infinite emitter, the template for Tracks A′
    and C.
  - A disproof kills stabilizer engines and localizes the programmability wall.
  - It is small, concrete, and a named MathOverflow question (339541).
