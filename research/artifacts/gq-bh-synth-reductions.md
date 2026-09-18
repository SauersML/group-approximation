# BH reduction ladder: synthesis (bh-synth-reductions, 2026-09-18)

This synthesis was written from origin/main at 9bf40a83a. It covers the 37 routes that
target `boone-higman-conjecture`, the equivalence and closure nodes, and the day's lane
landings.

Most nodes cited here are unreviewed lane proofs. Status words are copied from the nodes,
not re-derived; the one exception is the new node
`decidable-host-classes-reduce-to-canonical-kazhdan-groups`, which is proved.

**Headline.** Everything in the graph reduces to one question: does some finitely
presented Kazhdan-rich host contain explicit groups EL_3(Cantor crossed product)? The
only live route that answers it with one host per input is the Leavitt-tensor route over
free minimal subshifts. Its load-bearing open input is dynamical: (E)/(P1), a free minimal
subshift of finite type on a finitely presented overgroup of the input. Everything else
on main is either an equivalent restatement, a closure theorem (which provably cannot
prove BH alone), or a dead route.

## 1. The equivalence layer

BH is equivalent to each item below (all ESTABLISHED on main unless noted).

| # | Equivalent form of BH | Node |
|---|---|---|
| E1 | every infinite fg computably presented simple group embeds in an fp simple group | `boone-higman-iff-infinite-simple-inputs` |
| E2 | every infinite fg simple Kazhdan (so FA) group with solvable WP embeds in an fp simple group | `boone-higman-iff-simple-kazhdan-decidable-inputs` |
| E3 | every H_Γ = EL_3(LC(2^{C(Γ)},F_2) ⋊ Z/2≀C(Γ)), for Γ decidable, embeds in an fp simple group | **new**: `decidable-host-classes-reduce-to-canonical-kazhdan-groups` |
| E4 | every infinite decidable fg group (equivalently every H_Γ) embeds in an fp just-infinite group | `boone-higman-iff-fp-just-infinite-hosts`, plus E3 |
| E5 | Local BH: for every fp decidable H and g ≠ 1 there is a map φ: H → fp simple with φ(g) ≠ 1 | `local-boone-higman-iff-boone-higman` |
| E6 | CGP Q4 (isolated hosts) ∧ Local BH | `boone-higman-iff-isolated-hosts-and-local-boone-higman` |
| E7 | EMB = DEC as Σ_3 index sets | `boone-higman-is-equality-of-two-sigma-3-index-sets` |
| E8 | the decidable-edge tower premise (OPEN node; its collapse part is drafted) | `decidable-edge-tower-premise-is-equivalent-to-boone-higman` |

The permutational form (PBH) has its own ladder.

| # | Statement | Node |
|---|---|---|
| P1 | PBH ⟺ every decidable group lies in an fp full clopen-transitive Cantor group | `permutational-boone-higman-iff-full-cantor-hosts` |
| P2 | PBH ⟺ every decidable group lies in an fp Γ ≤ Sym(X) containing Alt_fin(X) | `permutational-boone-higman-iff-finitary-alternating-hosts` |
| P3 | PBH ⟺ every H_Γ lies in B_A | **new** (Theorem 2.2 of the new node) |
| P4 | (BH ⇒ PBH) ⟺ every fp simple group satisfies PBH ⟺ BFFHZ Q3.4 (MIF envelopes) | `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh` |
| P5 | an fp simple S is of type (A) ⟺ S has a proper fg subgroup of finite bi-index | `fp-simple-type-a-actions-iff-finite-bi-index-subgroups` |
| P6 | PBH ⇒ BH | Zaremsky Cor. B, `type-a-action-gives-boone-higman-for-subgroups` |

Closure properties of the BH class 𝓑 reduce to three core statements. (JE): any two fp
simple groups embed in a common fp simple group. (SQ): S×S embeds in an fp simple group
for every fp simple S. (FZ): S*Z embeds in an fp simple group for every fp simple S.

| Closure of 𝓑 under | is equivalent to | Node |
|---|---|---|
| finite direct products | (JE) ∧ (SQ) | `boone-higman-closed-under-finite-direct-products`, Attempt 10 |
| free products | (JE) ∧ (FZ) | `bh-class-free-products-iff-joint-embedding-and-free-z` |
| products plus finite extensions | (JE) ∧ (FW) | `bh-class-finite-extensions-reduce-to-finite-simple-wreaths` |

## 2. Why closure theorems cannot finish the proof

This is the structural lesson of the day.

1. **Permanence closures collapse to their base.**
   - By `finitary-permanence-closures-collapse-boone-higman-to-base` and
     `mixed-permanence-closures-collapse-boone-higman-to-base`, closing any base class under
     subgroups, extensions, finite or infinite graphs of groups, products and unions reaches
     every decidable group only if the base already does. The reason is that simple width
     survives these operations.
   - The E8 node records the same collapse for tree towers.
   - Consequence: the day's closure theorems (centralizer amalgams, coset wreaths ⟺
     identity-edge HNN, graphs of groups over good edges, extensions with finite Out,
     products of hyperbolic groups, and more) enlarge the known class. None of them can
     prove BH by itself.
2. **The base must contain the canonical Kazhdan groups.**
   - By E3 and the Kazhdan filter (Theorem 3 of the new node), every universal host class
     contains the groups H_Γ.
   - So no class of amenable, Haagerup, residually finite, or "only finite Kazhdan
     subgroups" groups can be universal.
   - This single lemma kills: Thompson-type hosts F, T, V and V_{n,r}; CAT(0)-cube
     proper-action hosts; self-similar, automaton and fg-linear hosts; normal germ
     extensions of V in the Cor. 2.10 regime; amenable-orbit full groups; amenable hosts.
   - Each of these was killed separately on main by a different argument; they are all the
     same obstruction.

## 3. Status of the universal-envelope routes

| Route (target: BH) | Status | Why |
|---|---|---|
| Shell envelopes, regular action (`…via-fp-shell-envelopes`, `…shell-germ-stabilizers`) | alive only formally | fp envelopes are known only for virtually cyclic or eventually periodic inputs. For Kazhdan inputs the shell group must avoid FW, since window zero dies for co-Hopfian FW inputs at both signs (47becd6b0, 7a95cf6d5) and commuting windows die at every width (872c2039c, e851421ae). Only non-commuting windows N ≥ 1 remain. |
| Genuine-action shells | same | same FW obstructions |
| Houghton-like envelopes | nearly dead | Lifting from germs is refuted (6362d6c31). Finite presentation forces ν to be pinned by finitely many local near relators (dc5ec83c8). Generic, translation-polyhedral, strand-map and regular-copy bases all die (ca0acda7f, 97511bec8, 303ae8c25). Open: rotation/reflection enumerations of Z². |
| Germ Steinberg algebra | repaired, open | A is never simple; A/J is central simple (ab6480b6c). J is finitely generated iff J_p ⊂ K[Q] is. Open: finite presentation of A/J. |
| Leavitt tensor over fp central simple B ⊇ F_2[G] | open | premise `decidable-group-algebras-have-fp-central-simple-hosts` (algebra BH with K-vanishing) |
| **Leavitt units of rigid SFT overgroups** | **open; three independent premises** | (E) dynamical, (K) K-theoretic, and the Khanh import. See §4. |
| V × aperiodic-SFT full groups | open | P1 (same dynamics as (E)) plus group-side finiteness P2. P1 ∧ P2 ⇒ (E) ⇒ P1, and this route gives PBH directly. |
| Rover–Nekrashevych hosts | DEAD | Deligne lattice and the Kazhdan filter |
| universal fp self-similar host | DEAD | residually finite |
| universal Leavitt host | DEAD | Weyl algebra obstruction in char 0; separate char-p kill |
| complexity-graded universal inputs; CK quotients; sandwich rings; maximal quotient | DEAD | see the nodes |
| isolated overgroup + Local BH; Bader–Shalom lattice hosts | open, reformulations | equivalent to BH (E6), no mechanism |

## 4. The master route

Route: `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`, with L = L_{F_2}(1,2).
1. **(E)** `decidable-groups-lie-in-fp-free-minimal-crossed-products`: G ≤ Λ, where Λ is
   finitely generated, X is a free minimal subshift over Λ, and B = LC(X,F_2) ⋊ Λ is finitely
   presented. This holds for a quantum rigid SFT over an fp Λ, by
   `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.
2. B is central simple, by `free-minimal-cantor-crossed-products-are-central-simple`.
3. **(K)** `free-action-leavitt-tensor-hosts-have-trivial-k1-k2`: K_1(B⊗L) = K_2(B⊗L) = 0.
   This is already ESTABLISHED when Λ is torsion-free Farrell–Jones, and when Λ is finite.
4. **Khanh import** (arXiv:2609.08428): (B⊗L)^× is finitely presented and simple.
5. Therefore G ≤ Λ ≤ B^× ≤ (B⊗L)^×.

**Why this route is canonical, not ad hoc.** The canonical Kazhdan inputs already sit in
(R_Γ⊗L)^×, via EL_3(R_Γ) ≤ GL_3(R_Γ⊗L) ≅ (R_Γ⊗L)^×, with R_Γ a Cantor crossed product
(Remark in the new node). The route replaces the finitely generated R_Γ by a finitely
presented Cantor crossed product over a larger group.

**Why char 2.** The scalar obstruction that killed the GL_n(Q) Steinberg-over-R_L quotients
does not arise here. That obstruction is `leavitt-scalar-commutators-block-fp-central-quotients`:
Q^× is central and not finitely generated. Over F_2 the scalars are trivial. So GL_n(Q)
(BBMZ 5.3(5)) should enter as a subgroup of Λ acting by units u_λ, not through its Q-linear
representation.

**(E) splits (route `minimal-free-sft-via-plane-constant-minimal-simulation`):**
- **(M2)** `decidable-fp-groups-have-effective-minimal-free-subshifts`: the Clapham envelope
  Λ_0 = Λ_1 × Z carries an effectively closed free minimal subshift. Equivalently, there is a
  computable point with free minimal orbit closure and a computable recurrence function.
- **(M1)** `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`: a group form of
  Durand–Romashchenko, lifting such a Y to a minimal SFT over Λ_0 × Z² with a free
  plane-invariant factor.

## 5. Ranked gates

Ranked by how much each unlocks times how tractable it is with current tools.

1. **Gate M2: effective free minimal subshifts on decidable groups.**
   - *Unlocks:* half of (E), and via (E) the master route.
   - *Tractability:* high. The Gao–Jackson–Seward construction of free minimal subflows of
     2^G (hyper-aperiodic points with uniform recurrence) plausibly becomes effective when
     the word problem is solvable. Aubrun–Barbieri–Thomassé give strongly aperiodic subshifts
     on every infinite fg group, and look for an effective version of their method.
   - *Source check first:* bounded arXiv search on "effective subshift" with Gao–Jackson–Seward
     or Carrasco-Vargas, and "strongly aperiodic subshift" with "decidable word problem".
2. **Gate M1: minimal simulation on Λ_0 × Z².**
   - *Unlocks:* the other half of (E).
   - *Tractability:* medium. Ingredients are Barbieri's simulation theorem for direct products,
     Barbieri–Sablik–Salo self-simulable groups (arXiv:2104.05141), Durand–Romashchenko
     quasiperiodic simulation (arXiv:1802.01461), and Labbé's minimal Wang shift as the Z² base.
3. **Gate K: K_1 and K_2 vanish for free actions.**
   - *Unlocks:* removes the Farrell–Jones restriction.
   - *Tractability:* medium. Try the Leavitt swindle (1 − 2 = −1) on K-groups together with
     K-regularity of LC(X) ⋊ Λ; LC(X) is regular, so the question is the NK-terms. The
     alternative is to choose Λ torsion-free Farrell–Jones inside the gates M1/M2 constructions.
4. **Gate A0: read Khanh arXiv:2609.08428 at source.**
   - *Why:* the whole Leavitt route, including the coNP^⊕P host of bh-free-26, is conditional
     on it.
   - *Tractability:* high and cheap.
5. **Gate T (calibration, not new content).**
   - *What:* run the pipeline end to end for Λ = Z² with Labbé's shift Ω_U. Here (K) is
     established because Z² is torsion-free Farrell–Jones, so the only question is quantum
     rigidity of Ω_U (`free-minimal-rigid-sft-via-labbe-shift`).
   - *Why:* a Z² success proves the machine works and is also the fp input of
     `labbe-shift-derived-full-group-is-finitely-presented`.
6. **PBH-side gates, not needed for BH:**
   - BFFHZ Q3.4 (MIF envelopes);
   - whether the Leavitt-tensor unit groups (B⊗L)^× have type (A) actions on Chen-module lines,
     which is known for L_{F_p}^× (`leavitt-unit-groups-mod-scalars-satisfy-pbh`). A yes turns
     the master route into a PBH proof.
7. **Closure gates:** (JE), (SQ), (FZ), decidable-edge HNN permanence, and finite central
   extensions. They shape the class but are provably insufficient alone (§2).
8. **Deprioritize.** Shells and Houghton-like envelopes: the remaining openings are narrow and
   the Kazhdan filter bites. Case-by-case class results (Artin types, 3-manifolds, test groups)
   become corollaries once the master route closes.

## 6. Lessons (also appended to board/LESSONS.md)

- L1. BH ⟺ every H_Γ = EL_3(LC(2^{C(Γ)},F_2) ⋊ Z/2≀C(Γ)) lies in an fp simple group. The
  same canonical-input reduction holds for PBH, just-infinite hosts, isolated hosts, and the
  dynamical premise P1/(E).
- L2. Amenable, Haagerup, residually finite, and "finite-Kazhdan" host classes are never
  universal. Thompson-type dynamics alone cannot prove BH. Any universal host must be
  Kazhdan-rich, i.e. algebraic: units or Steinberg groups over Cantor crossed products, or SV
  over Kazhdan actors.
- L3. Closure theorems collapse to their base class, so they calibrate BH but cannot prove it.
- L4. The master route is (E) ∧ (K) ∧ Khanh. Its load-bearing input is symbolic dynamics: a
  free minimal SFT on an fp overgroup of the input, split as M2 (effective minimal free
  subshift) plus M1 (minimal simulation one Z² factor up).
- L5. Work in characteristic 2: the non-fg central scalars Q^× that block char-0 Steinberg
  quotients vanish over F_2. Route GL_n(Q) through (E), not through R_L.

## 7. Suggested lane assignments

These are suggestions for the coordinator, not actions taken.
- M2: two lanes. One on an effective Gao–Jackson–Seward construction (computability plus
  combinatorics); one on the literature and an effective Aubrun–Barbieri–Thomassé route.
- M1: two lanes. One on Barbieri–Sablik–Salo self-simulation plus Durand–Romashchenko
  minimality; one on the Labbé-based Z² factor construction.
- K: one lane (algebraic K-theory of Leavitt tensors of crossed products).
- A0: one lane reads Khanh at source and discharges the conditional.
- T: one lane on Labbé calibration (quantum rigidity of Ω_U).
- PBH upgrade: one lane on type (A) actions of (B⊗L)^× on Chen lines.
