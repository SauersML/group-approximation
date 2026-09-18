---
rg: 2
id: higman-clapham-envelopes-are-hnn-over-machine-times-input
kind: claim
title: A benign pair for the relators makes the Higman envelope an HNN extension of (machine group x input) whose only machine-input coupling is the graph of F -> G; with decidably benign data, (D) of the envelope reduces to (D) of the input and of the machine, and the seed gate reduces to seed(G) plus one seed-coded HNN
requires:
  - decidable-free-subshifts-pass-to-graphs-of-groups
  - clapham-fp-embedding-preserves-word-problem
distinct_from:
  decidable-free-subshifts-pass-to-graphs-of-groups: that is the combination theorem for (D) along any finite graph of groups with decidable data; this applies it to the one splitting every Higman envelope carries, and isolates what the machine side must supply.
  clapham-fp-embedding-preserves-word-problem: that is the existence of a decidable fp envelope; this fixes the envelope's last splitting explicitly and states the decidable-membership premise (DB) that the (D) transfer and the seed transfer need.
  every-re-normal-subgroup-of-a-free-group-is-type-f-benign: that asks for type F benign witnesses; this asks for decidable ones, and uses them for subshifts, not for finiteness properties.
---

**ESTABLISHED** for §§1–3 (lane proof, bh-invent-14, 2026-09-18; the Higman step is classical, made
explicit here; not reviewed). §4 is a precise premise that is **not verified**. §5 is the seed-gate
reading for SYNTHESIS v6 (b5ad39956).

## 1. The envelope's last splitting

Let `G = F/N`, with `F = F(a_1, …, a_n)`. Call `(K, L)` a **benign pair** for `N` when `K ⊇ F` is
finitely presented, `L ≤ K` is finitely generated, and `L ∩ F = N` (Higman: `N` is benign when it
is r.e.).
- Let `H = ⟨K, t | t^{-1} l t = l, l ∈ L⟩`, which is finitely presented. Put `F' = t^{-1}Ft`.
- **Britton.** `⟨F, F'⟩ = F *_N F'`. A product `f_1 t^{-1} f_2 t ⋯` with the `f_i ∈ F \ N` has no
  pinch, because a pinch needs `f_i ∈ L ∩ F = N`.
- Let `π : F *_N F' → G` be `f ↦ f̄` and `f' ↦ 1`. It is well defined because `N̄ = 1`.
- In `B = H × G`, put `M_2 = ⟨F, F'⟩ × 1` and `M_1 = {(m, π(m))}`, the **graph of `π`**.
  `φ(m, 1) = (m, π(m))` is an isomorphism `M_2 → M_1`, since the first coordinate is injective.
- **The envelope.** `P = ⟨B, s | s^{-1} x s = φ(x), x ∈ M_2⟩`.

**Theorem 1.** `P` is finitely presented and contains `G`, as a direct factor of the base `B`.

*Proof.* Take the relations of `H`, the commutators `[h_j, ā_i]`, `s^{-1} a_i s = a_i ā_i`, and
`s^{-1}(t^{-1} a_i t) s = t^{-1} a_i t`. For `r ∈ N`, the element `r(a)` lies in `L`. So
`t^{-1} r(a) t = r(a)` follows from the relations of `H`, and conjugating both sides by `s` gives
`r(a) r(ā) = r(a)`. Hence every relator of `G` follows. The finite presentation therefore defines
`P`, and `G ≤ B ≤ P` by the HNN normal form. ∎

## 2. Decidability transfer

**(DB), decidably benign.** `K` has solvable word problem, membership in `L` is decidable in `K`,
and membership in `⟨F, F'⟩` is decidable in `H`.

**Theorem 2.** Assume (DB) and that `G` has solvable word problem. Then:
- `P` has solvable word problem;
- membership in the vertex group `B` and in the edge groups `M_1`, `M_2` is decidable in `P`;
- membership in `K` and `L` is decidable in `H`.

*Proof.*
- Britton reduction in `H` needs membership in `L`. Britton reduction in `P` needs membership in
  `M_1` and `M_2` inside `B` and the map `φ`.
- `(h, g) ∈ M_2` iff `g = 1` and `h ∈ ⟨F, F'⟩`.
- `(h, g) ∈ M_1` iff `h ∈ ⟨F, F'⟩` and `π(h) = g`. Once `h` is known to lie in `⟨F, F'⟩`, search
  for a word in the `a_i` and `t^{-1}a_i t`. Its `π`-image is a word in the `ā_i`, and it is
  compared with `g` by the word problem of `G`.
- `φ` is computable the same way. ∎

**Corollary 3 ((D) transfer).** Assume (DB). If `K` and `G` have (D), then so does `P`.
- The combination theorem (`decidable-free-subshifts-pass-to-graphs-of-groups`) gives (D) for `H`
  from (D) for `K`.
- Products give (D) for `B = H × G`.
- The combination theorem again gives (D) for `P`.

So **(D) of the envelope needs (D) of the input and (D) of the machine, nothing else.**

## 3. The input cannot be removed

`G` is a direct factor of the base, so it is elliptic in the splitting. If `G` has (FA), for
instance if it is Kazhdan, then `G` is elliptic in every splitting of every stage
(the (FA) lemma of the combination node).
- (D) of the envelope never follows from trees alone.
- The input's own (D) is the input-dependent part of E1's effectivity core (free form).

## 4. The machine side: premise (DB) + (D)(K), unverified

`N` is recursive exactly when `G` is decidable, and (DB) asks for a benign pair that *sees* this.
- **The naive Higman tower.** Higman's closure operations build the benign pair through
  projections of r.e. sets. So the associated subgroups of intermediate stages can have
  undecidable membership even when `N` is recursive. There the combination theorem cannot be
  applied stage by stage.
- **A decider tower (proposed).** Take a *total* reversible decider `M` for `N`. Its reachability
  and halting sets are decidable, by running `M` for the computable time the input size allows.
  - Recalled, not re-read: in Aanderaa–Cohen's modular-machine proof of Higman's theorem, the
    machine group is an HNN extension of `Z^2` along subgroups of `Z^2`.
  - At that level (D) holds unconditionally, by the combination theorem: lattice membership is
    decidable and `Z^2` has (D).
  - The later levels amalgamate along the halting subgroups. For a total decider their membership
    reduces to running `M`.
- **This is where Clapham consumes decidability.** Checking it at source, with (DB) and a
  decidable hierarchy of `K` stated as the output, is the next step. If it holds, the free form of
  E1's effectivity core is exactly (D) for the input.

## 5. What the tower does for seeds (v6 gate (SEED), CAP)

The seed class `𝒞` is closed under `×` and `∗` (SYNTHESIS v6). So by §1:

`seed(P) ⇐ seed(H) ∧ seed(G) ∧ [𝒞 is closed under the one HNN along (M_2, M_1)]`.

1. **The only coupling is `M_1 = graph(π)`.**
   - `M_2` lives in the machine factor, so it is input-free.
   - `M_1` is the graph of the quotient map `F *_N F' → G`. Seed-coding it means that the seed of
     `H × G` locally recognizes the pairs `(m, π(m))`. That is exactly where the input's word
     problem enters a seed's language.
   - So the CAP test of rung 1c has a sharp form at the envelope: **is the graph of
     `F *_N F' → G` seed-codable in `seed(H) × seed(G)`?** If CAP holds, the answer is no for inputs
     beyond the cap.
2. **Emitters are coset marks.**
   - `M_i` has infinite index in `B`, so the Bass–Serre tree of `P` has infinite emitters.
   - In the free form they cost nothing: the orientation of the combination theorem works at any
     valence.
   - In seed form, a sink or out-edge must be a finite pattern. That happens iff the vertex seed
     marks the out-coset, i.e. iff the indicators of `M_1` and `M_2` are definable by local rules
     relative to the seed.
   - So v6's "finite-type repair of emitters" is the same statement as "seed-coded associated
     subgroups", and the envelope needs it for exactly one pair.
3. **The input's seed is irreducible.** For (FA) inputs, `seed(G)` itself is needed (§3; v6
   gate 2).
4. **Summary.** For a Clapham envelope, (SEED) splits into:
   - `seed(G)`, which is input-dependent geometry;
   - `seed(H)`, the machine, input-free in shape;
   - one HNN closure along `graph(π)`, which is where the word-problem complexity of `G` must be
     written into local rules.

## Lesson for general BH

**A Higman envelope has one coupling.** After the benign machine is built, the envelope is an HNN
extension of `(machine) × (input)`, and the machine and the input meet only in the graph of the
quotient map `F → G`.
- Every transfer principle (free subshifts, seeds, rigidity) therefore splits into three parts:
  the input alone, the machine alone, and one HNN along `graph(π)`.
- Trees, and the infinite emitters of this HNN, are free in the free form. In seed form they cost
  exactly one seed-coded subgroup pair.
- So CAP is decided at the envelope by asking whether local rules can write the graph of the
  input's quotient map. A seed that can do so carries the input's word problem in its language,
  which is the carrier principle made concrete.

## Referee (bh-ref-ffwz, 2026-09-18): §§1–3 PASS; §4 correctly marked unverified

- **§1, Theorem 1: PASS.**
  - The subgroup `⟨F, t^{-1}Ft⟩ = F *_N F'` follows from Britton: a pinch needs `f ∈ L ∩ F = N`.
  - `π` is well defined on the amalgam, since both copies of `N` map to 1.
  - `φ` is an isomorphism onto the graph `M_1`.
  - The finite presentation is correct even though `B = H × G` is not finitely presented.
    Conjugating `t^{-1} r(a) t = r(a)` by `s` gives `r(a) r(ā) = r(a)`, using that each
    `ā_i` commutes with `H`. So every relator `r(ā)`, `r ∈ N`, is derived, and the finite
    presentation defines `P`.
  - `G ≤ B ≤ P` by the HNN normal form.
  - This is Higman's final step (Proc. R. Soc. A 262 (1961)), in the form of Lyndon–Schupp,
    *Combinatorial Group Theory*, Ch. IV §7. It should be credited as classical; the node's
    contribution is the explicit shape and the bookkeeping.
- **§2, Theorem 2 and Corollary 3: PASS.**
  - Britton reduction in `H` and `P` needs exactly the listed memberships and `φ`, `φ^{-1}`.
  - `π(h)` is computed by searching for a word for `h` in `a_i, t^{-1}a_i t`. The search
    terminates because membership is already known and `H` has solvable word problem.
  - Corollary 3 is a legitimate application of the combination theorem:
    - (H1)–(H3) for `H` (vertex `K`) and for `P` (vertex `B`) are supplied by Theorem 2;
    - vertex groups are finitely generated;
    - (D) for `B` comes from the product rule.
  - The word-problem half is Clapham's theorem (Proc. LMS 17 (1967)), recorded in
    `clapham-fp-embedding-preserves-word-problem`.
- **§3: PASS.** A direct factor of a vertex group is elliptic. The (FA) lemma is Serre's;
  Kazhdan implies (FA) by Watatani (1982).
- **§4.** The node rightly states (DB) and (D)(K) as unverified premises.
  - Aanderaa–Cohen modular machines are recalled, not read at source. Their exact form
    (HNN extensions of `Z²` along lattice subgroups) should be checked against Aanderaa–Cohen
    (1980) or Lyndon–Schupp IV.7 before §4 is upgraded.
  - (DB) is exactly the gap between "benign" and "decidably benign". It is the right thing to
    isolate.
- **§5.** This is interpretation, with no claims to check.
