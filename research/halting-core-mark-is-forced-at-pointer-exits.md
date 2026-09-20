---
rg: 2
id: halting-core-mark-is-forced-at-pointer-exits
kind: claim
title: In every anchored configuration the halting core mark on E-cosets is forced in both directions by transport plus one exit rule at the top vertex of each E-coset's subtree; the exit rule needs no computation for outgoing pointers (P ⊆ A°) and only a rope-and-residue split reader for incoming pointers, so the machine enters only at the sink
distinct_from:
  digit-paths-only-transport-the-halting-core-mark: that computes the core bit of an E-coset with nonempty trace at the sink vertex and leaves cosets with empty trace open; this forces the bit for every E-coset, empty trace included, by exit rules at non-sink vertices.
  coupled-rope-reader-has-nested-one-bit-fibres: that couples the free chains of the numeral reader on K_M; this uses its forced rope marks as the only input of the incoming-pointer exit rule, and records why its linking pattern cannot be copied onto E-cosets.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - digit-paths-only-transport-the-halting-core-mark
  - reordered-aanderaa-cohen-tower-has-fg-associated-subgroups
  - coupled-rope-reader-has-nested-one-bit-fibres
```

**ESTABLISHED for Theorem 1 and Lemma 2 (lane proof, bh-g1-universal-point, 2026-09-19; elementary, not
reviewed).** Part 3 is OPEN. This is the digit-path half of the core-mark split on seed-tower.md.

**Notation** (as in the required nodes).
- `B_1 = HNN(H_1; a_i : A° → A_i°)` with `a_i⁻¹ u a_i = φ_i(u)`, where:
  - `A° = F(t,x) * F(b) * ⟨d⟩`;
  - `A_i° = ⟨t_i, x^m⟩ * F(b) * ⟨d⟩`, free on `{t_i, x^m, b_j, b_i d}`;
  - `H_1 = K_M * (C × F(b)) * ⟨d⟩`.
- `T_1` is the Bass–Serre tree of `B_1`. At a vertex `gH_1`:
  - the **outgoing** `i`-edges are the cosets `zA°`, crossed by `z ↦ z a_i`;
  - the **incoming** `i`-edges are the cosets `zA_i°`, crossed by `z ↦ z a_i⁻¹`.
- `E = ⟨t, a_i⟩`, with `E ∩ H_1 = P = ⟨t_α : α ∈ I⟩ ⊆ F(t,x) ⊆ A°`. The coset `zE` meets the vertex `zH_1` in
  its **trace** `zP`, and meets exactly the vertices of the subtree `zT_E`, where `T_E = E·H_1`.
- **Base configurations** are those of the glued relative seed for `(B_1, P_±)`.
  - In an *anchored* configuration there is a unique **sink** vertex carrying the `(H_1, P_±)` pattern.
  - Every other vertex `v` carries a **pointer**: an edge coset `M_v` (`wA°` or `wA_i°`), marked on its elements
    by the vertex relative seed and naming the edge toward the sink.

## 1. The rules and the forcing theorem

The core mark `𝔪 ∈ {0,1}` lives on elements of `B_1`, and should equal `[zE ∩ P_± ≠ ∅]`. The rules are:
- **(T) Transport.** `𝔪(z) = 𝔪(zt) = 𝔪(z a_i)`.
- **(S) Sink.** At sink elements, `𝔪(z) = ν_±(z)`, where `ν_± = [z ∈ P_± P]`. This is a forced layer of the
  enriched sink seed, on the K_M side (bh-invent-15).
- **(O) Outgoing exit.** At a vertex whose pointer is `M_v = wA°`: if `z ∉ wA°`, then `𝔪(z) = 0`. This is local,
  because `z ∈ wA°` is exactly the edge-seed mark at `z`.
- **(I) Incoming exit.** At a vertex whose pointer is `M_v = wA_i°`: if `ν_i(z) = 0`, then `𝔪(z) = 0`. Here
  `ν_i(z) = [z ∈ wA_i° P]` is a forced layer of the enriched vertex seed for `(H_1, A_i°)`. The layer is
  left-`A_i°`-invariant, so the stabilizer does not change.

**Theorem 1.** In every anchored configuration whose layers `ν_±` and `ν_i` take their forced values, the rules
force `𝔪(z) = [zE ∩ P_± ≠ ∅]` at every element `z`. The forced point satisfies all four rules.

*Proof.*
- **Crossing criterion.** The coset `zE` crosses the pointer edge of a non-sink vertex `v`, at a trace element
  `z'`, iff `z'P ∩ M_v ≠ ∅`.
  - For `M_v = wA°`, since `P ⊆ A°`, this says `z' ∈ wA°`.
  - For `M_v = wA_i°`, it says `z' ∈ wA_i°P`.
  - In both cases the crossing is by a letter `a_i^{±1} ∈ E`, so it stays inside `zE`.
- **Sink inside the subtree.** If the sink `v_s` lies in `zT_E`, pick `z' ∈ zE ∩ v_s`.
  - By (T), `𝔪(z) = 𝔪(z')`, and by (S) this equals `ν_±(z')`.
  - By `digit-paths-only-transport-the-halting-core-mark` (Lemmas 1–3), this is the core bit.
- **Sink outside the subtree.** Otherwise let `v_0` be the vertex of `zT_E` nearest `v_s`, i.e. the projection of
  the sink onto the subtree.
  - Its pointer edge leaves `zT_E`, so by the crossing criterion (O) or (I) fires at `z'' ∈ zE ∩ v_0`.
  - By (T), `𝔪(z) = 0`.
  - `zE` misses the sink vertex, so it misses `P_± ⊆ H_1`, and it is not core.
- **The forced point satisfies the rules.** At a non-sink vertex of `zT_E` with `v_s ∈ zT_E`, the pointer edge
  lies on the path to `v_s`, inside `zT_E`. So (O) and (I) never fire on core cosets. ∎

**Both directions of the certificate.**
- *Value 1* comes only from (S), on the machine side.
- *Value 0* comes from (S) (nonempty trace, `ν_± = 0`) or from one exit rule at the top vertex (empty trace).
- The forcing is non-local: the top vertex or the sink may be far along `zE`. This is consistent with
  `seed-evaluation-is-bounded-by-the-forcing-radius`.

## 2. The incoming exit needs no machine

**Lemma 2.** Let `g ∈ H_1` have Kurosh normal form `g = g' g_k`. Then `g ∈ A_i° P` iff one of:
- `g_k ∈ K_M`, every syllable of `g'` lies in the corresponding factor subgroup of `A_i°`, and
  `g_k ∈ ⟨t_i, x^m⟩P`;
- `g_k ∉ K_M` and `g ∈ A_i°`.

For `k ∈ K = T ⋊ ⟨x,y⟩` with `T` free on `t(r,s) = y^{-s}x^{-r}t x^r y^s`, and `Q_i = ⟨t(β,0) : β ≡ i mod m⟩`:
- `k ∈ ⟨t_i, x^m⟩P` iff `k = x^a σ` with `m | a`, `σ ∈ T`, and the reduced `T`-word of `σ` is `u·v`;
- here `u` uses only letters `t(β,0)` with `β ≡ i (mod m)`, and `v` only letters `t(α,0)` with `α ∈ I`.

*Proof.*
- **Syllables.** The first part is the proof of Lemma 2 of the required node, word for word. It uses that
  `A_i°` is a free product of subgroups of the three factors, and that `P ⊆ K_M`.
- **Normal form.** `⟨t_i, x^m⟩ = Q_i ⋊ ⟨x^m⟩`, because `x^{-c} t(β,0) x^c = t(β + c, 0)`. So
  `⟨t_i, x^m⟩P = {q x^{mr} p} = {x^{mr} (x^{-mr} q x^{mr}) p}`.
  - `x^{-mr} Q_i x^{mr} = Q_i`, since the shift is `≡ 0 (mod m)`.
- **Membership.** Hence `k ∈ ⟨t_i,x^m⟩P` iff `k = x^a σ` with `m | a` and `σ ∈ Q_i P`.
- **Product of free factors.** `Q_i` and `P` are spanned by subsets of the free basis of `T`. An element lies in
  the product of two such subgroups iff its reduced word is a prefix over the first subset followed by a suffix
  over the second. Cancellation only removes letters of the intersection. ∎

**Consequences.**
- The exit mark `ν_i` is a two-phase split automaton ("prefix, then suffix") run along reduced `T`-words.
- Its letter tests are:
  - a residue mod `m`, which is local;
  - the rope mark `[α ∈ I]`, forced at linear radius by bh-invent-15's coupled reader
    (`coupled-rope-reader-has-nested-one-bit-fibres`);
  - `[k ∈ K]`, one Bass–Serre pointer of `K_M`'s seed (`seeds-record-every-bass-serre-pointer`).
- **No halting set enters `ν_i`.** The only layer that depends on the machine is `ν_±` at the sink, through
  `𝔠 = [g ∈ ⟨U⟩P]`.

**The E′ side.** The same Theorem holds for `E' = ⟨td, a_i⟩` with `P' = ⟨e_α⟩`, since `P' ⊆ A°`.
- Rule (O) is unchanged.
- `ν'_i = [· ∈ A_i° P']` and `ν'_± = [· ∈ P_± P']` are not computed here. `P'` is diagonal across the free
  factors (`e_α = t_α w_α(b) d`), so Lemma 2's syllable split does not apply. This is OPEN.

## 3. End-type configurations (OPEN; the free bit of gate RR)

- **Where free bits arise.** If the pointers converge to an end `ξ`, rule (S) never fires. (O) and (I) force
  `𝔪 = 0` on every `E`-coset with a top vertex. The cosets whose subtree contains a ray to `ξ` keep a free bit.
- **(RS1) is unaffected.** The seed cylinder contains only anchored configurations. So Theorem 1 already gives
  isolation of the forced point for the core-mark layer.
- **Naive linking is wrong.** One cannot link the free bits of cosets through one marked `A°`-coset, as the
  coupled reader links sibling blocks.
  - Take `z` with `z a_i = 1` at a sink. Then `zE` is core (`ν_±(1) = 1`).
  - `zxE` crosses to `z a_i x^m = x^m`, and `ν_±(x^m) = [x^m ∈ ⟨U⟩P] = 0`.
  - The reason: `⟨U⟩ ∩ K ⊆ T` and `P ⊆ T`, while `x^m ∉ T`.
  - So the rule `𝔪(z) = 𝔪(zx)` fails in the forced point.
- **What remains.** The free bits at `ξ` are limits of `ν_±` on the traces at a receding sink. So (RS2) needs
  joint realizability of `ν_±`-patterns (bh-free-56's (FS)). (RS3) needs these bits to be central against the
  base.
- **Centrality test (sketch, not checked).** Use bh-invent-15's visibility theorem
  (`free-bit-components-are-central-iff-they-see-the-base`, 9459f6eaa).
  - A free bit here is shared by one `E`-coset whose subtree contains a ray to `ξ`. The thickened coset
    therefore contains the pointer spine toward `ξ`.
  - With (RS1) for every vertex seed, the spine determines `ξ`, and `ξ` determines the whole base.
  - So Theorem A there should apply, and Theorem B's failure mode (the base changes outside the support)
    should not occur.
  - What must still be checked is that the local transfer steps of the theorem reach the spine inside a bounded
    thickening of the coset.

## Lesson for general BH

- **Certify "not core" at the exit.** A two-sided core mark on HNN edge cosets is certified at the top vertex of
  each coset's subtree, where the coset fails to cross the base pointer. It is not certified along the coset.
- **Why that is cheap.** The crossing test is a double-coset mark `[z ∈ M_v Q]`, for the pointer's edge coset
  `M_v` and the trace group `Q`.
  - When `Q` lies inside the pointer's edge group (`P ⊆ A°`), the test is the pointer mark itself.
  - Otherwise, Kurosh normal form turns it into a split automaton over the rope marks.
- **Where the machine enters.** Only at the sink. The machine-independent exits are finite-state over the rope
  reader.
- **Where the freedom goes.** All remaining freedom sits in end-type configurations, as free bits on the cosets
  that run to the end. They cannot be linked along the base, but each such coset carries the spine, which is
  exactly the visibility that centrality needs.

## Correction (bh-g1-universal-point, 2026-09-19): rigidity is inherited-refuted; forcing stands

bh-invent-15's `cohen-rope-reader-is-not-quantum-rigid` (1208f63aa) refutes quantum rigidity of the Cohen rope
reader. The rigid seed records no `x`-positions below the sink, so the digits are extension data. Once the absorbing
state `bad` is reached, the reader is blind to them, and far branches switch independently.

**What survives.**
- Theorem 1 and Lemma 2 are statements about forced values in anchored configurations, i.e. about (RS1).
- They do not use rigidity and stand as written.

**What is refuted.** Two things:
- **(RS3) for the core-mark layer, as designed.** The rope marks are a consumed input of `ν_i`.
- **Blindness in `ν_i` itself.** Determinized, the split automaton of Lemma 2 has states such as `prefix`,
  `suffix` and `reject`.
  - `reject` is absorbing, and it is blind to the positions of later letters.
  - Those positions are the same unrecorded `x`-data.
  - So `ν_i` has the blind-state defect independently of the rope reader.
  - Only the outgoing exit (O), which reads the pointer mark alone, is free of it.

**Consequence for the design.** An exit rule that is rigid under gate (GL-rigid) needs an injective, group-language
reader. Two routes are open:
- Replace the split test `[σ ∈ Q_i P]` by a group-language invariant that detects crossing. A prefix/suffix
  split is not a group language, so this needs a new invariant, not a new automaton.
- Choose the tower so that every non-core coset exits through an **outgoing** pointer, where (O) is local.
  - That holds if trace groups lie in both edge groups at every vertex.
  - Here `P ∩ A_i° = φ_i(P) ≠ P`, so it fails.

**Lesson.** Forcing and rigidity separate at readers. An absorbing state is harmless for (RS1) and fatal for (RS3)
whenever the data it ignores is extension data. Exit certificates must therefore be written as injective readers,
or read off a pointer.
