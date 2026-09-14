---
rg: 2
id: passive-fixing-injective-automata-surjective-proof
kind: route
title: Configurations with finitely many active sites split into finite invariant pieces that are dense
target: passive-fixing-injective-automata-are-surjective
requires: []
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
---

Complete direct proof. Notation as in the target: `Φ` is an injective cellular automaton on `C^G`, and
`P ⊆ C` is nonempty.

1. **Finite pieces.** For a finite set `E ⊆ G` and `ω ∈ P^(G \ E)` put
   `X(E, ω) = { x ∈ C^G : x = ω on G \ E, and x(g) ∉ P for every g in E }`.
   It has `|C \ P|^|E|` elements.
2. **`Φ` maps each piece into itself.** Let `x ∈ X(E, ω)`.
   - At `g ∉ E` we have `x(g) = ω(g) ∈ P`, so `Φ(x)(g) = ω(g)`.
   - At `g ∈ E` we have `x(g) ∉ P`, so `Φ(x)(g) ∉ P`.
   So `Φ(x) ∈ X(E, ω)`.
3. **Each piece lies in the image.** `Φ` restricts to an injective map from the finite set `X(E, ω)` to
   itself, which is a bijection.
4. **The pieces are dense.** Let `p` be a pattern on a finite set `F ⊆ G`, and fix `z ∈ P`. Extend `p` by
   `z` outside `F` to a configuration `x`. Put `E = { g ∈ F : p(g) ∉ P }` and `ω = x` on `G \ E`. Then
   `x ∈ X(E, ω)` and `x` lies in the cylinder of `p`.
5. **Conclusion.** `Φ` is continuous and `C^G` is compact, so `Φ(C^G)` is closed. By steps 3 and 4 it
   contains a dense set, so `Φ(C^G) = C^G`.

No property of `G` is used, and the memory and local rule of `Φ` are arbitrary.

**Model tests** (artifact, Section 2).
- Both hypotheses are needed. The left shift on `{0,1,*}^Z` writes active symbols into passive sites.
  The rule "output `*` wherever a neighbour is `*`" writes passive symbols at active sites. Neither piece
  `X(E, ω)` is then invariant, and step 2 is where the argument stops.
- The theorem does not contradict any landed strict transfer. The product-alphabet rules of
  `strict-rule-pairs-pass-to-product-alphabets` use no reserved symbol. The passive-block involution codes
  of `passive-block-involution-codes-ascend` work at table level, not on a full shift with fixed sites.
