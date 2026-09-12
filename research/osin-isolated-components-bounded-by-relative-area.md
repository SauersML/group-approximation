---
rg: 2
id: osin-isolated-components-bounded-by-relative-area
kind: claim
title: In a relatively hyperbolic group the peripheral lengths of isolated components of a cycle are bounded linearly by its relative length
distinct_from:
  hyperbolic-group-relative-to-maximal-elementary-subgroup: that supplies one relatively hyperbolic structure on a word-hyperbolic group; this is Osin's bound on isolated peripheral components of cycles, valid for any finite reduced relative presentation.
---

**ESTABLISHED** (literature import) through `osin-isolated-components-relative-area-citation`.

Let `G` be hyperbolic relative to a collection of subgroups `{H_λ}` in Osin's sense. That is, `G` has a finite relative presentation `<X, {H_λ} | R>` with linear relative Dehn function, and it may be taken reduced. Then:
1. **Finite peripheral alphabet.** The set `Omega_λ` of elements of `H_λ` represented by `H_λ`-syllables of relators is finite.
2. **Isolated components are short.** There are constants `M, C, C'` such that the following holds for every cycle `q` in `Gamma(G, X ∪ H)` and every set `p_1, ..., p_k` of isolated `H_λ`-components of `q`:
   - `phi(p_i) in <Omega_λ>`;
   - `sum_i |phi(p_i)|_(Omega_λ) <= M Area^rel(q) <= M (C l(q) + C')`.

**Generating set.** The finite relative generating set `X` may be enlarged by finitely many elements, each with one relator. The relative Dehn function changes only within its equivalence class, which is Osin's remark on p. 7 citing his Theorem 2.34, so it stays linear.

**Terms.** A component is a maximal subpath labelled by `H_λ`-letters. Two components are connected when vertices of both lie in one left coset `g H_λ`. A component is isolated when no other component is connected to it.

Consumer: `fpbs-twisted-level-percolation-disconnected-proof`.
