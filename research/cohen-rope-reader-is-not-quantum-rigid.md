---
rg: 2
id: cohen-rope-reader-is-not-quantum-rigid
kind: claim
title: Over the rigid scaling seed, x-positions on descendant cosets are extension data; with Cohen's absorbing rope automaton the reader can sit at "bad" everywhere, and then the positional digits of far-apart subtrees switch independently, so the coupled rope reader is not quantum rigid at any scale
distinct_from:
  free-bit-components-are-central-iff-they-see-the-base: that proves centrality from visibility and states, in Corollary C, rigidity of the coupled reader under a hypothesis (H); this shows (H2) fails, because positions are not base data, and that the reader is in fact not rigid.
  coupled-rope-reader-has-nested-one-bit-fibres: that proves linking and pointwise rigidity with the positional layer frozen; this puts the positional layer back into the fibre and finds independent switches there.
  absorbing-rope-readers-are-not-pointwise-rigid: that retracted node blamed merging words for unlinked reader bits, wrongly; this finds the real failure of absorbing readers, in the positional layer they fail to couple.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
  - coupled-rope-reader-has-nested-one-bit-fibres
  - free-bit-components-are-central-iff-they-see-the-base
```
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-19; elementary; not reviewed). It answers the
coordinator's request to prove (H) of `free-bit-components-are-central-iff-they-see-the-base`:
- **(H1)** holds;
- **(H2)** is false as it was used;
- **Corollary C** there (the coupled reader is quantum rigid) is **refuted**. Theorems A and B
  there stand.

## Setting
- **The base.** `Y_0` is the rigid seed of `locally-finite-splittings-preserve-rigid-sft-compactifications`
  for the scaling part `S_M`, a multiple HNN extension of `A = Z^2`. It consists of pointer labels,
  and a `C_Z ⊠ C_Z` point on the sink coset only.
- **Edges.** Recall `l^{-1} x^m l = x` and `l^{-1} y^m l = y^{m^2}`. A coset has `m^2` children,
  `h z l A`, and `m^2` parents, `h z l^{-1} A`. The parents are indexed by
  `A/⟨x, y^{m^2}⟩`, so they are invariant under `x`.
- **The positional layer `M_K`.** On every coset of the region `R`, `M_K` records, for each
  element, its `x`-position residue mod `m^{K+1}` relative to the coset origin, together with
  `C_Z ⊠ C_Z` origin markers. `K ≥ 0`, and `K = 0` is layer M of
  `modular-machine-scaling-seed-reads-regular-numerals`. `M_K` may be any SFT extension that is
  correct on the forced point.
- **The reader.** `X = Y_0 + M_K + (ρ, q)` is the coupled reader of
  `coupled-rope-reader-has-nested-one-bit-fibres`, over Cohen's automaton (`bad` is absorbing).

## Theorem
1. **(H1) holds.** Every configuration of `Y_0` has a unique sink coset or a unique end, and the
   pointers are the tree directions to it. This is §2 ("Orientation") of
   `locally-finite-splittings-rigid-compactification-proof`, which is already landed.
2. **(H2) fails as used.**
   - `Y_0` carries no `x`-position on non-sink cosets. On a coset of `R`, the pointer is an
     `l^{-1}`-edge label in `A/⟨x, y^{m^2}⟩`, and by rule (T) it is invariant under `x`.
   - So the digits the reader reads are data of the extension `M_K`, not of the base.
   - (H2) counted them as base data, so Corollary C's decomposition used a base, `Y_0 + M_K`,
     that is not the rigid one. Part 3 shows that this base is not rigid either.
3. **Independent positional switches.** Fix `y ∈ Y_0` with sink coset `S` whose `x`-marker is
   `−^Z` (origin at infinity). For every `D` there is a `y`-relative `D`-family of `X` that does not
   commute. Hence `X` is not `D`-quantum rigid for any `D`, by item 2 (lifting) of
   `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`. The same family works for
   `Y_0 + M_K` alone.
4. **What survives.**
   - Theorems A and B of the parent.
   - Linking, and pointwise rigidity of `(ρ, q)` with `M_K` frozen.
   - The rope marks are still forced at linear radius on the seed orbit.

   What fails is rigidity of the whole construction. So the reader **closes no rung** of the
   seed tower.

## Proof of 3
**Net depth.** For a coset `C`, follow the tree path from `S` to `C`.
- An `l`-child step divides `x`-shifts by `m`. A parent step, or an `r`-step (`x^m ↦ x^{m^2}`),
  multiplies them by `m`.
- Let `e(C)` be the number of dividing steps minus the number of multiplying ones.
- So `g_N = x^N ∈ A` fixes every coset with `m^{e(C)} | N`, and it shifts that coset's positions
  by `N/m^{e(C)}`.

**Two configurations.**
- Let `x ∈ X` be a limit of translates of the forced point with the sink origin pushed to
  infinity, chosen so that the limiting `m`-adic reference position has infinitely many bad
  digits.
  - Then every reader chain meets bad digits, so `q ≡ bad`, and `ρ = 1` on `R`.
  - All cosets have their origin at infinity, so their markers are `−^Z`.
- Put `x' = g_N · x` with `N = c·m^{d+1+K}`, `c ≢ 0 mod m`. It lies over the same `y`: the base is
  invariant under `x`-translation on `S`, and pointers are preserved.
- **Agreement.** For `e(C) ≤ d` the shift is divisible by `m^{K+1}`. So residues mod `m^{K+1}` and
  markers agree, and `x = x'` there. The reader layer is `bad` in both.
- **Difference.** At `e(C) = d+1` the residues move by `c·m^K ≢ 0 mod m^{K+1}`, so `x ≠ x'` there.

**Gluing.** Take `W > 2D`, and a coset `C_u ∈ R` with `e(C_u) = d − W`.
- Define `x^{(u)}` as `x'` on the branch of `C_u` (the side of its edge toward `S` not containing
  `S`) and `x` elsewhere.
- **The differences stay apart.** Inside the branch, `x` and `x'` differ only at `e ≥ d+1`, that
  is at tree distance `> W` from the cut edge. Outside, they differ at the same depth, also
  beyond distance `W`. Each tree step costs a stable letter, so no `D`-ball meets differences on
  both sides.
- **Validity.** Every `D`-window of `x^{(u)}` is therefore a window of `x` or of `x'`, and
  `x^{(u)} ∈ X`, since `X` is an SFT.
- **The reader.** The reader rules hold, because `q ≡ bad` is compatible with every digit (`bad` is
  absorbing), and `(L)` compares `bad` with `bad`.

**Two switches.** Choose a second such coset `C_{u'}` whose branch lies at tree distance `> 2D`
from the branch of `C_u`, which is possible since `R` branches.
- The four configurations `x`, `x^{(u)}`, `x^{(u')}`, `x^{(u,u')}` all lie in `X` over `y`, by the
  same window argument.
- Their difference sets are the two deep parts of the branches, at distance `> 2D` from each other.

**The family.** On `k^2`, take noncommuting idempotents `Q, Q'`.
- At a site of switch 1 whose letters differ, give `Q` to the letter of `x` and `1 − Q` to the
  letter of `x^{(u)}`. Do the same with `Q'` at switch 2, and use scalars elsewhere.
- (Q1) and (Q2) hold, since supports farther apart than `2D` never meet.
- (Q3_y) holds: a window meets at most one switch, and there the product is nonzero only on
  restrictions of the configurations above.
- `Q` and `Q'` do not commute. `∎`

## What this means for gate RR and the seed tower
- **Why the reader fails.** Absorbing readers decouple from the positional layer. The
  configuration `q ≡ bad` makes the reader blind to digits, and digits of far-apart subtrees are
  then free and independent.
- **What a rigid reader needs.** It must read the positions **injectively**, so that every
  positional switch shows up in `q` and hits a link `(L)` at the switch's boundary.
  - With a group (permutation) automaton, the local switch above is not admissible. Changed
    digits change `q` up to `C_u`'s row, and `(L)` against `C_u`'s unswitched siblings forbids it.
  - So the counterexample is gone. Rigidity is **OPEN** there. It is the new gate
    **(GL-rigid)**: rigidity of positional layer plus injective reader.
- **Gate (GL).** Cohen's rope set (digits in `{1,…,2n}`) is not a group language: merging words
  exist, which is the true part 1 of `absorbing-rope-readers-are-not-pointwise-rigid`. So a rigid
  seed tower needs a Higman–Clapham tower whose infinitely generated steps are indexed by group
  languages, or by residue-periodic sets, which are read by deterministic factors.
- **Rung status.**
  - Step 1 of the build order (a rigid, linear-forcing reader on `K_M`'s scaling part) is **not
    closed**.
  - It is closed only relative to a frozen positional layer.
  - The live gates are (GL-rigid) and (GL).

## Lesson for general BH
- **Positions are fibre data.** Coordinates that a rigid seed does not itself record (here,
  `x`-positions below the sink) are extension data, with free digits at infinity. Distant
  subtrees switch their digits independently unless some layer reads them injectively and
  links the result.
- **The two tests for a free datum.** A reader that can go blind, by sitting in an absorbing
  state, leaves positional freedom unlinked and destroys rigidity. The rule "free data must see
  the anchor" (visibility) therefore applies to every layer the reader consumes, not only to
  the reader's own bit.
