---
rg: 2
id: halting-pair-seeds-need-a-two-sided-core-mark
kind: claim
title: In the halting pair (B_2, A_±) both input pieces are graphs over one seed of C (graph lemma), but seeds are not coarsely dense in the digit-letter edge cosets, so the core mark on those cosets must be certified in both directions; the negative direction is gate RR, and it needs a mortal machine run along digit paths
distinct_from:
  mikhailova-relative-seeds-push-down-to-bi-seeds: that treats fibre products and proves the diagonal trick; this extends the trick to graphs of arbitrary homomorphisms and applies it to the input vertex of the halting pair.
  reordered-aanderaa-cohen-tower-has-fg-associated-subgroups: that makes every associated subgroup finitely generated and isolates (B_2, A_±) as the CAP pair; this locates the single non-local ingredient of a relative seed for that pair.
---

**ESTABLISHED for 1 and 2 (lane proof, bh-g1-universal-point, 2026-09-18; elementary, not reviewed). Part 3 is a
design consequence.** Notation is that of `reordered-aanderaa-cohen-tower-has-fg-associated-subgroups`:
- `B_2 = HNN(B_1, p : E → E')`, with `E = ⟨t, a_i⟩` and `E' = ⟨td, a_i⟩` (both free of rank `2n+1`);
- `A_± = HNN(P_±, p : ⟨t_α⟩_{I_0} → ⟨e_α⟩_{I_0})`;
- `P_+ = ⟨U⟩ * ⟨d⟩ * F(b)` and `P_- = ⟨U⟩ * ⟨d⟩ * ⟨b_j c_j⟩`, inside
  `H_1 = K_M * (C × F(b)) * ⟨d⟩`.

## 1. Graph lemma: the input pieces need only a one-sided seed of `C`

**Lemma.** Let `C` have a seed `(Z_C, p_C, z_*)`. Let `H` be finitely generated, with generators `h_j`, and let
`φ : H → C` be a homomorphism with graph `Γ_φ = {(φ(h), h)}`. Then `(C × H, Γ_φ)` has a relative seed satisfying
(RS1).

**Proof.** This is the diagonal trick of `mikhailova-relative-seeds-push-down-to-bi-seeds`, with the graph in place
of the diagonal. Define the SFT `Y` by two kinds of rules.
- **(R1) Rows.** Each `C`-row `c ↦ y(c, h)` obeys the rules of `Z_C`, i.e. right multiplication by `(s,1)`.
- **(R2) Propagation.** "`p` at `g`" holds iff "`p` at `g·(φ(h_j), h_j)`" holds, where "`p` at `g`" means
  `y(g(b,1)) = p_C(b)` on the seed ball. Each `φ(h_j)` is a fixed word, so this rule is local.

A point with `p` at `1` then has `p` on all of `Γ_φ`. So row `h` has its seed at `φ(h)`, and by isolation in `Z_C`
it equals `φ(h)·z_*`. Hence the point is forced to be `y_*(c,h) = z_*(φ(h)^{-1}c)`, and
`Stab(y_*) = {g : p at g^{-1}} = Γ_φ`. ∎

**Application to the input vertex `C × F(b)`.**
- *Plus side.* `A_+ ∩ (C × F(b)) = 1 × F(b)`, the graph of `φ = 1`.
- *Minus side.* `A_- ∩ (C × F(b)) = ⟨b_j c_j⟩`, the graph of the presentation map `b_j ↦ c_j`. This is a
  Mikhailova-type graph; its push-down is a bi-seed of `C`.
- The lemma supplies both sides from one ordinary seed of `C`. So the two sides `±` put **no** two-sided demand on
  the input. Only (RS1) is claimed: rows without a seed are not coupled, as in the diagonal trick.

## 2. Non-density lemma: seeds are sparse in the core edge cosets

**Lemma.** For every `k ≥ 1`, the element `a_1^k ∈ E` has `B_1`-distance at least `k` from `P_±`. The same holds
for `E'`.

**Proof.**
- Suppose `a_1^k = g u` with `g ∈ P_± ⊆ H_1`. Then `u = g^{-1} a_1^k`.
- This word is Britton-reduced for `B_1 = HNN(H_1; a_i)`, since two equal-sign stable letters never pinch. So it
  has exactly `k` stable letters.
- Every word for `u` contains at least `k` stable letters (Britton), so `|u| ≥ k`. ∎

**Meaning for a relative seed of `(B_2, A_±)`.**
- *Which edges are core.* The `A_±`-core of the Bass–Serre tree of `B_2` has, at the vertex `B_1`, the p-edges
  through the cosets `hE` with `h ∈ P_± E`. Only these edge cosets carry seeds. By the reasoning of bh-star-a's
  pointer lemma (`seeds-record-every-bass-serre-pointer`), a relative seed must record, on every such edge coset,
  whether it is core. This step is a sketch: that lemma is proved for seeds with trivial stabilizer.
- *The core mark.* Record this as `𝔪(h) = [h ∈ P_± E]`.
  - It is constant on each coset `hE`, by transport along `t` and `a_i`.
  - It is forced to `1` on cosets containing a seed, by propagation.
- *What the lemma kills.* The base coset `E` is core, since `1 ∈ P_±`. Yet it contains points `a_1^k` at distance
  `≥ k` from every seed.
  - So no rule of the form "`𝔪 = 1` ⇒ a seed within radius `R`" can hold.
  - Hence the value `0` of `𝔪` cannot be forced by seed proximity.
- *The failure mode.* A configuration that sets `𝔪 = 1` on a seedless coset obeys every rule that only propagates
  seeds. So does the spurious core component that this setting glues on across the p-edge. Such a gluing is not
  isolated, and (RS1) fails.

## 3. What a relative seed for the halting pair must contain

**Both values of the core mark need certificates.**
- **The value 1** is certified by seed propagation. It is local, via transport along the coset.
- **The value 0** needs a certificate carried along the coset.
  - For `h ∈ H_1`, the subgroup lemma gives `hE ∩ P_± ≠ ∅` iff `h ∈ P_± P`, with `P = ⟨t_α : α ∈ I⟩`.
  - So the certificate must decide membership in `⟨U⟩·P`, i.e. the halting set read on base-`m` digit numerals.
  - A certificate that terminates for **every** configuration is exactly the lead's mortality condition (T1, via
    `every-decidable-set-has-a-mortal-decider`): a mortal decider gives a finite rejecting run.
  - The reader must therefore run along the digit-letter paths `W` of each `E`-coset. There
    `W^{-1}tW = t_{α(W)}`. The run happens there, not only on `K_M`'s sheet.

**Link to gate RR (bh-invent-15, 5a72aa6a9).**
- A seedless `E`-coset with an unforced mark is an unanchored chain carrying one free bit. This is exactly the
  phenomenon of gate RR.
- Fix (b) there, a co-deterministic reader, is the same thing as the negative certificate here.
- So gate RR and the core mark of the halting pair are one gate. Solving RR for the numeral reader with the
  **mortal** decider in place of a regular automaton would supply the core mark.

**Link to the reversible space-time layer (bh-free-56).**
- That layer must be placed on the digit paths of `E`-cosets as well as on `K_M`'s configuration sheet.
- Its rigidity is needed on both. The two meet at `t_α`, where the `E`-coset path `W` and the `K_M`-sheet point
  `(α, 0)` are identified by `W^{-1}tW = x^{-α}tx^{α}`.

## Lesson for general BH

- **Passing an edge costs a two-sided certificate.** A relative seed for a subgroup whose core crosses an HNN edge
  must certify both answers of "is this edge coset core?".
- **Why both.** Seeds certify "yes" by propagation. When the subgroup is sparse in the edge group, as the halting
  subgroup `⟨t_α⟩_{I_0}` is in the free edge group `⟨t, a_i⟩`, "no" cannot come from proximity. It must be a
  terminating computation.
- **The input side is easy.** Graphs of homomorphisms over a seeded group, including the Mikhailova-type minus
  side, need only a one-sided seed.
- **Where CAP is decided.** It is decided exactly where the mortal decider meets the digit paths, which is also
  where gate RR's free bit lives.
