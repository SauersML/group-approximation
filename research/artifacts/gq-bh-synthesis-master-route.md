# Boone–Higman: master route (synthesis v3, 2026-09-18)

Lead synthesis of the 09-18 BH swarm (lane `bh-synth-lead`).
- **Earlier versions.** v1 12a123bf1. v2 b344473a1 merged the reductions (87daac9eb),
  obstructions (5f923fc28) and hosts (03663c211) syntheses.
- **What v3 corrects.** The route and the gate ranking, after the first gate reports:
  - bh-algebra, `free-crossed-leavitt-k-gate-is-a-farrell-jones-instance` (c8180598b);
  - bh-free-25, `deterministic-time-lifts-inherit-quantum-rigidity` (f13c0975b);
  - bh-free-32, the complexity caps (0343a8459, 44ba929bc);
  - bh-g3-libridge (85f1ca34a);
  - bh-g2-buildings (c1df2182b);
  - bh-verify-master, all five load-bearing nodes PASS (c9f9d0769).

This is a strategy document, not a proof. Cited nodes are mostly unreviewed lane proofs, and
their status lines govern. The live lane table is in `board/SYNTHESIS.md`.

## 0. Thesis (v3)

**Unchanged.**
- **The local rigidity principle (LRP).** A host is fp only if its global structure is the
  unique solution of finitely many local rules. Every kill is a non-rigid model; every
  success is a rigid finite-type coding.
- **The missing theorem, FTR.** Finite type plus local rigidity implies finite
  presentation, for *non-deterministic* codings. It is proved ring-side
  (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`); group-side it is P2′.
- **The dynamical object (★).** A quantum-rigid free minimal SFT.

**Corrected in v3.** The ring side's K-gate is not a technicality: it is *exactly* one
Farrell–Jones instance for the acting group. That splits the master route into two tracks
that differ in **where the input sits**.
- **Track A (group side, primary).** The input G sits inside the acting group Λ ⊇ Λ₀ ⊇ G.
  - *Needs:* (★) over Λ and the group-side FTR (P2′).
  - *Needs no Farrell–Jones.*
  - *Gives:* PBH.
  - *Complexity* enters through WP(Λ₀).
- **Track B (ring side over a fixed Farrell–Jones group).** The acting group P is fixed
  (Z², Z²×F₂, F₂×F₂, a CMSZ lattice), and G sits in the *ring units* of B⊗L.
  - *Needs:* (★) over the one fixed group P, with a **programmable** language, plus an
    algebraic embedding gate U.
  - *K is free* (Farrell–Jones holds for P), and the ring-side FTR is proved.
  - *Complexity* enters through the language L(X).
- **Discarded.** The mixed version, ring side with G ≤ Λ, needs Farrell–Jones for groups
  containing arbitrary decidable groups. It survives only as a conditional theorem (§4).

**Common crux.** Both tracks need **(★) over Z²-type groups**, and Track B needs it with a
programmable language. The Z² rigidity gate, first a calibration in v1, is now
load-bearing for both tracks.

## 1. LRP evidence and design rules (v3)

| Kind | Node | Mechanism |
|---|---|---|
| kill | `free-shift-houghton-like-envelopes-are-not-fp` | generic enumeration locally stable |
| kill | `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators` | fp ⇒ ν unique solution of local rules |
| kill | `fp-pl-groups-with-f-have-no-transcendental-support-endpoints` | deform the parameter |
| kill | `fp-alternating-full-groups-of-free-subshifts-force-sft` | fp ⇒ finite type |
| kill | `v-times-golden-silver-wang-product-full-group-is-not-fp` | independent faults translate apart |
| kill | `thick-building-flat-sfts-are-never-quantum-rigid` | thickness: a half-apartment lies in two apartments (independent faults) |
| kill | `fp-v-times-subshift-full-groups-force-quantum-rigidity` | operator models must commute |
| kill | `annular-free-product-germ-hosts-are-not-finitely-presented` | no depth n → n+1 rule |
| success | `finitely-coded-cantor-actions-give-type-a-hosts` | (UFP\*) unique factorization |
| success | `a2-lattices-embed-in-fp-simple-groups` | pencil closure (local → global) |
| success | `deterministic-time-lifts-inherit-quantum-rigidity` | a deterministic direction propagates rigidity |
| success | `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` | rigidity suffices (ring side) |

**Design rules.** Rules 4, 5 and 8 are new or corrected in v3.
1. **Rank ≥ 2, one-ended.** Rigid N-codings are periodic; rank-one hosts confine zero sets.
   - *Framing fix from verify-master:* properness and zero-set confinement are *two* walls.
2. **No independent far faults.** Products must be coupled (golden–silver), and flat
   codings of thick buildings are never rigid.
3. **Never rely on amenability of Λ in Track A.** Osajda-type inputs make Λ₀ non-exact.
4. **Where complexity may sit (corrected).**
   - *Terminology.* "Units act residually finitely" (hosts lane) concerns the **isotropy
     groups of the coding category** in coded groupoids, and it holds. "Load complexity into
     the units" (bh-algebra) concerns the **ring units** of B⊗L, a much larger group; L^×
     alone is non-sofic. The two do not conflict.
   - *The rule.* Complexity may sit in WP(Λ₀) (Track A) or in L(X) together with the ring
     units (Track B). It may never sit in coding isotropy, or in any finite-state normal
     form: finite-state Li-coded full groups have WP in 2^{Cl²} (bh-g3-libridge).
   - *Consistency.* This matches bh-free-32: in minimal free SFT hosts, hardness enters only
     through WP(Λ₀) or L(X).
5. **Where the Kazhdan input enters.** In Track A, by global Λ-inclusion. In Track B, as
   ring units: EL₃ of a subring, which is Kazhdan by Ershov–Jaikin.
6. **Central classes need free codings.**
7. **Q-divisibility sits in Λ (Track A) or in the ring (Track B),** never in dynamical
   masses. Over F₂, Q^× is never a scalar.
8. **Deterministic time is free (new).** A time-deterministic direction inherits rigidity
   from its rows (bh-free-25). So over Λ₁ × Λ₂, G2 reduces to a rigid free row SFT over Λ₂
   plus a jointly free minimal action by automorphisms. Over F₂ as the *space* factor, no
   free lift exists (Piantadosi), so F₂×F₂ needs a genuinely coupled rule.

## 2. Track A (primary): the input in the acting group, group-side finiteness

```
G decidable
 └ G0  Clapham: Λ₀ ⊇ G fp, solvable WP                 [supplied]
   └ G1  Λ = Λ₀ × H, free minimal SFT X on Λ            [OPEN] M2 + rigid M1
     └ G2  X quantum rigid                             [OPEN]
       └ P2′ (group FTR): A(G_V × Λ⋉X) fp                [OPEN; the one finiteness gate]
         └ G4: simple, type (A) ⇒ PBH for G             [supplied]
```

- **G0.** For BBMZ 5.3(5), take Λ₀ = St₁₀(R_L). Its Q^× is a central subgroup of Λ.
- **G1.**
  - *M2:* an effective minimal free subshift on Λ₀.
  - *Rigid M1:* a coupled Durand–Romashchenko simulation over Λ₀ × Z² that *preserves*
    rigidity.
  - *Why rule 8 helps:* it lets the Z² factor be space and Λ₀ act as deterministic time
    only if Λ₀ ≤ Aut(Y) for a rigid Z²-SFT Y. That is the cleanest design to test: X = the
    time lift of (Y, Λ₀-action).
- **G2 over Λ = Λ₀ × Z².** By rule 8, this reduces to **a rigid free minimal SFT Y over Z²
  whose automorphism group contains Λ₀ acting jointly freely and minimally.**
  - *Known constraint:* low-complexity minimal SFTs have small automorphism groups, so Y
    needs a rich automorphism group.
  - *Candidate:* fixed-point tilings, whose automorphisms can be programmed.
- **P2′ (promoted).** This is now Track A's *only* finiteness route; the ring-side FTR would
  require Farrell–Jones.
  - *What won't work:* the Li bridge. Finite-state normal forms cap the WP at 2^{Cl²}
    (bh-g3-libridge).
  - *What must be proved:* a **finiteness theorem that produces no normal form.** One option
    is Brown's criterion on a Stein–Farley complex of prefix-tree × pattern-cylinder
    partitions, with descending links controlled by rigidity (unique local extension) rather
    than by a normal form (bh-g3-steinfarley, jointly with the non-LCM dissection gate
    for 𝒯_m and 2V_Λ). The other is non-finite-state RF units of type F₂.

## 3. Track B (secondary, independent): a fixed Farrell–Jones group, the input in ring units

```
P fixed (Z² first; Z²×F₂, F₂×F₂ or a CMSZ group as fallback), all Farrell–Jones
 └ B1  a family X_W of rigid free minimal SFTs over P whose languages encode any decidable W   [OPEN]
   └ ring FTR: B_W = LC(X_W,F₂) ⋊ P fp                           [PROVED given B1]
     └ K: K₁ = K₂ = 0 for B_W ⊗ L                                [PROVED: FJ for P]
       └ A0 Khanh import: (B_W ⊗ L)^× fp simple                   [conditional; read at source]
         └ U  G ↪ (B_W ⊗ L)^×, for W = WP(G)                      [OPEN]
```

- **B1 = G2 over a fixed P with programmability.**
  - *Why it looks feasible:* Durand–Romashchenko already make every effective minimal
    Z-subshift a projective subaction of a minimal Z²-SFT. So minimal Z²-SFT languages have
    unbounded complexity.
  - *What is missing:* only rigidity. That is exactly the G2-fp conjecture (§6) for
    programmable fixed-point tilings, which bh-g2-fixedpoint-a is testing.
- **U, a Kirchberg–Higman embedding (new name for the gate).**
  - *The statement:* every fg decidable G, or every canonical H_Γ = EL₃(R_Γ), embeds into
    the ring units of B_W ⊗ L for the W that encodes it.
  - *A reduction:* since M₃(L) ≅ L, a unital ring embedding R_Γ ↪ B_W ⊗ L suffices, and
    then H_Γ ≤ EL₃(B_W ⊗ L).
  - *Why this is the analogue of Kirchberg:* exact C\*-algebras embed in O₂. Here the tiling
    carries the input's computation, and L supplies the Cuntz isometries.
  - *It merges two earlier items:* Strategy 2 (algebra BH) and
    `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`.
- **Risks.**
  - (i) An exactness-type heredity for ring-unit groups over an amenable P is unknown either
    way. If it exists, it forces the fallback P = F₂×F₂, which is Farrell–Jones but needs a
    coupled rigid SFT (rule 8).
  - (ii) U has no mechanism yet.

## 4. The conditional theorem (the discarded mixed version)

With G ≤ Λ on the ring side:

> BH ⇐ (★ over Λ₀ × H for every decidable Λ₀) ∧ (Farrell–Jones with coefficients for those Λ)
> ∧ Khanh.

This follows from `free-crossed-leavitt-k-gate-is-a-farrell-jones-instance` together with the
ring-side FTR. Farrell–Jones is conjectured for *all* groups. So this makes BH a consequence of
one dynamical statement plus two believed conjectures. It is not a proof route, but it is
evidence that BH is true (§7).

## 5. Strategy 3 (backup), unchanged

- **The equivalence.** BH ⇔ PBH via BFFHZ Q3.4 or FFWZ Q5.9 (bh-typeA-universal repairs the
  FFWZ stabilizer gap).
- **The gap.** The Titz Mite–Witzel kernel is the only recorded fp simple group not known to
  be in B_A (bh-testcases).
- **The limit.** Closure theorems calibrate BH but cannot finish it.

## 6. The G2-fp conjecture (serves both tracks)

**The shared ingredient.** Three lessons ask for a rule carrying depth n to depth n+1:
bh-free-22, Ã₂ pencil closure, and (★). A self-simulating fixed-point tiling has such a rule
at every level.

> **Conjecture (G2-fp).** A fixed-point tiling with locally unique parse is quantum rigid.

**Proof strategy.** Induction on levels. A commuting operator family on level-(k−1)
supertiles extends uniquely to one on level-k supertiles, the operator version of unique
parsing.

**What it gives each track.**
- *Track B:* fixed-point tilings are programmable, so G2-fp over Z² is B1 outright.
- *Track A:* it supplies rigid Y, and its programmable automorphisms are the candidates for
  Λ₀ ≤ Aut(Y).

**Calibration warnings.**
- The golden–silver and thick-building kills show that any certificate must exclude
  independent far faults. Unique parse is the property that does this.
- Rule 8: the deterministic time direction must not be free space over F₂.

## 7. Gate ranking v3 (decisiveness × tractability) and lanes

| Rank | Gate | Track | Lanes (see board) |
|---|---|---|---|
| 1 | **G2 over Z², programmable** (G2-fp; Labbé; permutive) | A and B | bh-g2-fixedpoint-a, bh-g2-labbe, bh-g2-permutive |
| 2 | **P2′, a group FTR with no normal form** (+ non-LCM) | A | bh-g3-steinfarley, bh-free-29 |
| 3 | M2, effective minimal free subshifts on decidable fp groups | A | bh-g1-effective, bh-free-37 |
| 4 | U, the Kirchberg–Higman embedding into (B_W⊗L)^× | B | bh-algebra, bh-free-53 (both redirected here from K / S2) |
| 5 | G2 over Λ₀×Z² via time lifts (rich Aut(Y)) and rigid M1 | A | bh-g1-simulation, bh-g1-rigidsim, bh-free-25 |
| 6 | A0, Khanh at source | B and §4 | bh-free-26 |
| 7 | Non-amenable fixed P (coupled rigid SFT over F₂×F₂ or Z²×F₂) | B fallback | bh-g2-f2f2, bh-g2-fixedpoint-b |
| 8 | Obstruction side (all free minimal SFTs over some one-ended Λ) | both | bh-g2-obstruct |
| 9 | Boundary-shift candidate (only topologically free) | B (if the ring side extends to topologically free actions) | bh-g2-buildings |
| — | S3 backup; complexity map; verification | — | bh-typeA-universal, bh-testcases; bh-free-32; bh-verify-master, bh-refute |

**Changes from v2:**
- **Retired.** The Li bridge as a route to hard hosts: bh-g3-libridge's cap. It survives
  only for structured classes (MCG, Deligne).
- **Dropped.** Building-link rigidity arguments for flat SFTs.
- **Demoted.** G3r "K for arbitrary Λ". It is now the conditional theorem of §4, and
  bh-algebra moves to U.
- **Promoted.** P2′ to rank 2, and Z² rigidity from calibration to rank 1.

## 8. Reconciliation log

- **bh-algebra's Farrell–Jones gate.**
  - *Adopted:* it is exact. Hence the two-track split and §4.
  - *Its recommendation* ("fix Λ in a Farrell–Jones class, load complexity into X and the
    units") is Track B. It is viable complexity-wise: minimal Z²-SFT languages are
    unbounded (Durand–Romashchenko), and the units-route kill for free P does not apply
    to Z².
  - *Its conflicts with the hosts lane and bh-free-32 are only apparent* (rule 4): the hosts
    lane's "units" are coding isotropy, and bh-free-32 allows hardness through L(X).
- **Is the group side now primary?** Yes, for full BH. Track A is the only track that needs
  neither Farrell–Jones nor a new embedding theorem. Its price is P2′, which must be a
  finiteness theorem with no normal form. Track B is the independent second track whose
  dynamics lives over one fixed group.
- **bh-free-25.**
  - *Adopted as rule 8.*
  - *Over F₂×F₂:* only coupled rules work.
  - *Over Λ₀×F₂:* F₂ as time over a rigid free SFT on Λ₀. This re-routes Track A's G2 to
    "a rigid Y over Z² with Λ₀ ≤ Aut(Y)".
- **bh-g3-libridge.** Adopted in P2′ and in rule 4.
- **bh-g2-buildings.** Adopted in rule 2 and rank 9.
- **bh-verify-master.** Adopted: the load-bearing nodes are PASS, and rule 1 carries the
  framing fix.
- **From v2, still standing.**
  - Canonical inputs H_Γ, which explain the host's shape and now also give U its concrete
    form, R_Γ ↪ B_W ⊗ L.
  - The collapse theorems: closure theorems cannot finish.
  - M1 + M2 ⇏ (E), since rigidity is separate.
  - GL_n(Q) via St₁₀(R_L) as an acting group (Track A) or via U (Track B).
  - Zero-set confinement.
  - The complexity wall, equivalent to G2 plus a finiteness theorem with no normal form.
  - Hosts' "Li without lcms", now tied to P2′.

## 9. Assessment

**BH true: leaning yes, about 65/35 (unchanged).**
- **Mildly positive:** the conditional theorem in §4 derives BH from (★) plus Farrell–Jones
  plus Khanh, and Farrell–Jones is widely believed.
- **Mildly negative:** two cheap completions are gone. The Li bridge is capped, and the
  ring-side K-gate needs Farrell–Jones for arbitrary Λ. So a proof now needs one genuinely
  new finiteness theorem (P2′) or one new embedding theorem (U), in addition to (★).
- **The decisive objects:**
  - *Toward true, and serving both tracks:* one quantum-rigid free minimal SFT over Z² with
    a programmable language.
  - *Toward false:* a rigidity obstruction for all free minimal Z²-SFTs of unbounded
    language complexity, or a uniform word-problem bound for fp simple groups.
