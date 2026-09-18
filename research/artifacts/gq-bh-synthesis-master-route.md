# Boone–Higman: master route (synthesis v4, 2026-09-18)

Lead synthesis of the 09-18 BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62.
- **What v4 folds in:** two batches of gate reports (§8).
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane
  proofs, and their status lines govern. The live table is `board/SYNTHESIS.md`.

## 0. Thesis (v4): the carrier principle

**Still standing:**
- **LRP.** Finite presentation holds only if the global structure is the unique solution of
  finitely many local rules.
- **FTR.** Finite type plus rigidity gives finite presentation, for non-deterministic codings.
  - *Ring side:* proved.
  - *Full-group side:* only a necessity direction is proved.
- **(★).** A quantum-rigid free minimal SFT.

**New in v4.** The gate reports force one organizing fact, the **carrier principle**. The
input's *coarse geometry* and its *complexity* must both be carried by something in the host.
The reports show exactly one viable carrier: **the acting group Λ.**

1. **Complexity.** Finite-state codings cap the word problem at 2^{Cl²} (bh-g3-libridge).
   Coding isotropy acts residually finitely (hosts lane; bh-groupoid's degree-coboundary
   theorem). Hardness enters only through WP(Λ) or the language L(X) (bh-free-32).
2. **Geometry.** A move-table embedding of the input needs a translation-like action on the
   host group, so sep(input) ≲ sep(P) (bh-invent-09). Decidable monsters coarsely contain
   expanders. So a *fixed* host group carrying them must itself carry expanders, and for such
   groups Farrell–Jones is open. Track B's K-gate is then no longer free. The v3 split
   (ring side over a fixed FJ group) therefore survives only if gate U has a *non-geometric*
   mechanism.
3. **Non-amenability is forced three times.**
   - Over amenable Λ the Stein–Farley complex for P2′ is never cocompact (bh-g3-steinfarley).
   - The separation cap excludes amenable fixed hosts for expander-like inputs.
   - Osajda-type inputs make the envelope non-exact.
4. **Non-RF inputs must scale.** In a finitely coded groupoid, a group whose level cocycle is
   a coboundary acts residually finitely (bh-groupoid). So simple inputs must change level
   without bound, like a lattice acting on its boundary.

**Master route v4 (Track A, now clearly primary).**
- **Setup.** Put K′ = G × F₂, and let Λ₁ ⊇ K′ be a Clapham envelope: finitely presented, with
  solvable word problem, non-amenable. Let Λ = Λ₁ × Λ₁. This square is self-simulable by
  Barbieri–Sablik–Salo.
- **(E1) Existence.** A minimal free SFT X over Λ, from (M2) plus BSS Q:minimal (bh-g1-simulation).
- **(E2) Rigidity.** X is quantum rigid.
- **(E3) Finite presentation.** P2′ holds for non-amenable Λ, proved combinatorially.
- **Conclusion.** Then A(G_V × Λ⋉X) is a finitely presented simple group of type (A) containing
  G, which gives PBH.

**The Z² programme is demoted from gate to building block.**
- *Scale collapse (bh-free-12).* For self-similar SFTs, rigidity is a finite check at one scale
  ≤ 5.
- *Transport (bh-free-09).* Rigidity passes along products and deterministic extensions.
- *Transplants to non-amenable groups:*
  - the Busemann transplant to CMSZ lattices (bh-invent-04);
  - the ABH lift to F_n × Z (ABH 2204.11492).
- *Consequence:* a rigid Z² tile certified by a finite computation is how (E2) should be
  *built*.

## 1. LRP evidence (v4 additions marked +)

| Kind | Node | Mechanism |
|---|---|---|
| kill | `free-shift-houghton-like-envelopes-are-not-fp` | generic enumeration locally stable |
| kill | `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators` | fp ⇒ ν is the unique solution of local rules |
| kill | `fp-alternating-full-groups-of-free-subshifts-force-sft` | fp ⇒ finite type |
| kill | `v-times-golden-silver-wang-product-full-group-is-not-fp` | independent faults translate apart |
| kill | `thick-building-flat-sfts-are-never-quantum-rigid` | a half-apartment lies in two apartments |
| kill + | `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid` | two far modifications give a wall certificate |
| constraint + | `quantum-rigid-sfts-over-products-have-a-single-free-branch` | over Λ₀×H, extensions are free in at most one branch of H |
| kill + | `simple-subgroups-act-trivially-on-equicontinuous-factors` | no odometer parse, so deterministic couplings die |
| success | `a2-lattices-embed-in-fp-simple-groups` | pencil closure (local → global) |
| success + | `deterministic-extensions-of-rigid-sfts-are-rigid`, `quantum-rigidity-is-product-stable` | rigidity transports |
| success + | `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale` | rigidity at one scale ⇒ at all scales (the cross-depth rule, proved for substitutions) |
| success + | `telescope-fixed-points-are-singular-on-a-parse-shift` | the self-simulation equation has a unique solution |
| success | `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` | ring FTR |

**The G2-fp conjecture (v2/v3), now split.** Its cross-depth half is *proved* for block
substitutions: that is the scale collapse. What remains is a *finite* rigidity check at scale
≤ 5, or 3 for DRS Wang sets.

## 2. Track A (primary): gates

```
G ⊆ K′ = G×F₂ ⊆ Λ₁ (Clapham, fp, decidable, non-amenable);  Λ = Λ₁ × Λ₁
 ├ E1  existence of a minimal free SFT on Λ     = M2 (for Λ₁) + MSS (BSS Q:minimal on squares)   [OPEN, 2 premises]
 ├ E2  rigidity of that SFT                     [OPEN; build from rigid Z² tiles + transport]
 └ E3  P2′ for non-amenable Λ                   [OPEN; combinatorial proof needed]
     ⇒ A(G_V × Λ⋉X) fp simple, type (A) ⇒ PBH for G   [supplied]
```

**E1 (existence).** `minimal-free-sft-via-minimal-self-simulation-of-squares` gives
(M2) ∧ (MSS) ⇒ E1.
- *(MSS):* a restricted form of BSS's printed question Q:minimal for products of non-amenable
  groups. Lane bh-g1-bss.
- *(M2):* effective minimal free subshifts on Λ₁. Lanes bh-g1-effective, bh-free-37.
- *Calibration, known:* F_n × Z carries a minimal free SFT (ABH, read at source). CMSZ lattices
  carry free SFTs if the boundary shift is of finite type (bh-invent-04, conditional).

**E2 (rigidity) is now the sharpest open gate.**
- *Necessary conditions:*
  - no finite modification;
  - no far modifications;
  - a single free branch over every factor with ≥ 2 ends. So choose H one-ended, or check
    single-branch determinism;
  - no independent faults (golden–silver, thick buildings).
- *Sufficient tools:*
  - scale collapse (finite check);
  - product and deterministic-extension stability;
  - the Busemann transplant, whose partial result says germ marginals are classical, so what
    remains is a centrality condition (C).
- *First decisive tests:*
  1. **Is ABH's minimal free SFT on F_n × Z quantum rigid?**
     - *Why it's cheap:* existence is already known there, the group is non-amenable and FJ,
       and the single-free-branch condition is a quick necessary test.
     - *What each answer gives:* a yes gives the first rigid free minimal SFT over a
       non-amenable group; a no gives a precise kill.
  2. **A finite rigidity certificate at scale ≤ 5** for one self-similar Z² SFT (Labbé or a
     DRS Wang set). This is a noncommutative ideal-membership computation; bounded MSI search
     is appropriate.
  3. **The transplant (C)** for CMSZ lattices, given 2 and (H_Ω).
- *Why these matter:* 1–3 are the three independent ways to get a rigid non-amenable
  instance.

**E3 (P2′).** It has the LCM property, so it is *not* the non-LCM 𝒯_m gate; v3's pairing is
corrected.
- *The finiteness hierarchy* (bh-g3-steinfarley):
  - the Boolean inverse monoid is always fp;
  - the ring is fp iff X is rigid;
  - the full group is fp only if X is rigid.
  Golden–silver separates these levels, and quantum-family methods cannot decide P2′.
- *So P2′ needs a combinatorial proof, and over non-amenable Λ only.*
  - Lane bh-g3-tfc ("translation-finitely coded" SFTs).
  - bh-invent-06: telescopes and parse shifts force P2′-type finiteness on SFT singular sets.
- *Calibration:* F_n × Z with ABH's SFT, together with test E2.1.

## 3. Track B (ring side over a fixed FJ group): status after the carrier principle

**What still works.** The ring FTR holds, and K-vanishing holds for FJ acting groups. The
non-amenable FJ candidates are F_n × Z, F₂ × F₂ and CMSZ lattices, all CAT(0).

**Gate U.** It embeds G into the units of (B_W ⊗ L)^×.
- *Via move tables* (bh-invent-09): this is equivalent to a translation-like action of G on the
  acting group, so the separation cap applies. A universal fixed P must then carry expanders,
  and FJ for such P is open.
- *So Track B survives only with a non-geometric U.* That means ring units that don't come
  from bounded-displacement actions, such as EL₃ of subrings built from L's isometries and the
  tiling's computation. The universality question is lane bh-gate-u-wobble.
- *If no non-geometric U exists,* Track B merges into the conditional theorem of §4.

**Rank.** Track B stays open, ranked below Track A.

## 4. Conditional theorem (unchanged)

BH ⇐ (E1 ∧ E2 over the envelopes) ∧ (FJ with coefficients for those Λ) ∧ Khanh, by
`free-crossed-leavitt-k-gate-is-a-farrell-jones-instance` and the ring FTR. This route needs no
P2′. FJ is conjectured for all groups, so the remaining unknowns are dynamical (E1, E2).

## 5. Strategy 3 update: every recorded fp simple group is now in B_A

bh-verify-euclid passed the Euclidean-building theorem (84896de5e). So the Titz Mite–Witzel
kernels, previously the one recorded exception, lie in B_A.
- *Consequence.* Joint embedding, (SQ), (FZ), and product and free-product closure of the BH
  class hold for every *recorded* fp simple group. A counterexample to any of them now needs a
  new fp simple group.
- *Also passed:* referee-c passed Belk–Zaremsky Conjecture H and the FFWZ §1.2 criterion
  (488bd5ce1), where bh-typeA-universal repaired FFWZ.
- *Still open:* BH ⇔ PBH in general, i.e. BFFHZ Q3.4. Closure theorems still cannot prove BH by
  themselves (the collapse theorems).

## 6. Structured classes (off the universal path)

- **Cubulated (bh-major-cube-a).** A (UFP\*) degree map exists only for tree products
  (`commutative-cube-degree-maps-force-tree-products`). Li's (t<d) fails beyond them, so a new
  **Perron finiteness criterion** is needed (bh-invent-perron).
- **Closed MCG and Deligne.** These need the non-LCM dissection gate for 𝒯_m and 2V_Λ (MAJOR
  MCG, bh-free-55). It is *not* P2′.
- **Branch hosts.** They are annular hosts over V (bh-major-branch-a, b03b5e689). So they
  inherit the annular obstruction (no depth n → n+1 rule) unless they carry a recursive
  cross-depth relation (`fp-annular-germ-groups-are-hnn-recursive`).
- **S1b, re-scoped (bh-groupoid).** Boundary-type finitely coded actions over higher-rank
  building geometry, with complexity in residually finite F_∞ cell stabilizers. Only building-type
  geometry can carry non-RF Kazhdan inputs in a coding.

## 7. Gate ranking v4 (decisiveness × tractability)

| Rank | Gate | Lanes |
|---|---|---|
| 1 | **E2 on F_n × Z:** is ABH's minimal free SFT quantum rigid? (single-free-branch test first) | bh-g2-f2f2 (retarget), bh-g2-obstruct (necessary side) |
| 2 | **Finite rigidity certificate** at scale ≤ 5 for a self-similar Z² SFT (Labbé, DRS); bounded MSI ideal-membership search | bh-g2-labbe, bh-g2-fixedpoint-a, bh-free-12 |
| 3 | **E3: combinatorial P2′** over non-amenable Λ; F_n × Z calibration | bh-g3-tfc, bh-g3-steinfarley, bh-invent-06, bh-invent-06b, bh-free-29 |
| 4 | **E1: MSS** (BSS Q:minimal on non-amenable squares) | bh-g1-bss |
| 5 | **E1: M2** (effective minimal free subshifts on decidable fp groups) | bh-g1-effective, bh-free-37 |
| 6 | **E2 transport:** the Busemann transplant (C) to CMSZ; product and deterministic-extension constructions | bh-invent-04, bh-free-09, bh-g2-fixedpoint-b, bh-free-25 |
| 7 | **Gate U, non-geometric** (else Track B merges into §4) | bh-gate-u-wobble, bh-algebra, bh-free-53 |
| 8 | **A0:** read Khanh at source | bh-free-26 |
| 9 | **Obstruction side** (a kill for all minimal free SFTs over some one-ended non-amenable Λ) | bh-g2-obstruct |
| — | Structured: Perron criterion, non-LCM gate, branch/annular, S1b; S3; complexity map | bh-invent-perron, MAJOR teams, bh-groupoid, bh-typeA-universal, bh-free-32 |

**Retired in v4:**
- Time-lift / deterministic-coupling designs for simple inputs (no odometer parse).
- Z² as a Track A base (Stein–Farley is not cocompact there).
- Move-table U over amenable P.
- The v3 P2′/non-LCM pairing.

## 8. Reconciliation log (v4)

- **Batch 1:**
  - steinfarley, 0cf7b14de: LCM pairing fix; non-amenable Λ; the hierarchy; combinatorial P2′.
  - simulation, 05f066167: deterministic couplings dead; route via squares plus MSS.
  - bh-free-09, 5761d0db0 and 74ebc36f8: rigidity transport.
  - obstruct, ec68d6d47: finite-modification kill and single-free-branch constraint; no universal
    kill.
  - bh-groupoid, 05fca9eb0: degree coboundary ⇒ RF; non-RF inputs must scale; S1b re-scoped.
- **Batch 2:**
  - (a) ABH minimal free SFT on F_n × Z; existence there is done, which drives E2.1.
  - (b) Scale collapse: G2-fp becomes a finite check (rank 2).
  - (c) Busemann transplant to CMSZ, conditional on (H_Ω) (rank 6).
  - (d) Move-table U plus the separation cap give the carrier principle, item 2.
  - (e) Telescopes: a unique self-simulation solution with an SFT singular set, feeding P2′.
  - (f) Titz Mite–Witzel kernels in B_A; Conjecture H and FFWZ §1.2 PASS (§5).
  - (g) Perron criterion (§6).
  - (h) Branch = annular over V (§6).
- **Carried over from v2/v3:**
  - canonical inputs H_Γ;
  - collapse theorems;
  - M1 + M2 ⇏ (E);
  - GL_n(Q) via Λ₀ = St₁₀(R_L) inside K′;
  - zero-set confinement, with properness as a separate wall;
  - rule 4 terminology (coding isotropy vs ring units).

## 9. Assessment

**BH true: leaning yes, about 65/35.** The number is unchanged, but the reasons are sharper.
- **For:**
  - No gate report produced a universal kill. The obstruction lane found only local
    constraints: finite modifications, far faults, single free branch.
  - Existence of minimal free SFTs over non-amenable groups has literature support (ABH;
    BSS self-simulation).
  - Rigidity became a finite check for self-similar tilings.
  - Every recorded fp simple group is now in B_A.
- **Against:**
  - The carrier principle leaves one route (Track A). It needs three genuinely new theorems:
    MSS, a rigid free minimal SFT over a non-amenable square, and a combinatorial P2′.
  - No rigid free minimal SFT is known over any group.
- **The single most informative computation** is the rigidity of ABH's SFT on F_n × Z, together
  with a scale-≤5 rigidity certificate for one self-similar Z² tile.
