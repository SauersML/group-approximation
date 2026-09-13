---
rg: 2
id: outer-extension-isolated-via-centralizer-argument
kind: route
title: Every nontrivial normal subgroup contains the simple kernel, because the centralizer of the kernel lies in the kernel of Q → Out(S)
target: outer-extensions-of-fp-simple-groups-are-isolated
requires: []
---

Notation and imported statements as in the target.

**Finite presentation.** `I` is an extension of the finitely presented group
`S` by the finitely presented group `Q`, so `I` is finitely presented (the
closure of finite presentation under extensions, as stated by CGP in the proof
of Corollary `cor extensions_fd`, lines 1143–1145).

**Finite discrimination.** Let `N ⊴ I` with `N ≠ 1`.
- `N ∩ S` is normal in `S`, and `S` is simple, so `N ∩ S` is `1` or `S`.
- Suppose `N ∩ S = 1`. Both `N` and `S` are normal in `I`, so
  `[N, S] ⊆ N ∩ S = 1`, and `N ⊆ C_I(S)`.
- Let `c ∈ C_I(S)`. Conjugation by `c` is the identity automorphism of `S`, so
  the image of `cS ∈ Q` in `Out(S)` is trivial. That homomorphism is injective,
  so `cS = S`, that is `c ∈ S`. Then `c ∈ C_I(S) ∩ S = Z(S)`, and `Z(S) = 1`
  because `S` is nonabelian and simple. So `C_I(S) = 1`.
- Hence `N = 1`, a contradiction. So `N ∩ S = S`, i.e. `S ⊆ N`.

Pick `s ∈ S − {1}`. Every non-trivial normal subgroup of `I` contains `S`, hence
`s`, so `F = {s}` is a finite discriminating subset. By the CGP Proposition
(lines 554–557), `I` is isolated.

**The split case.** For `φ: Q → Aut(S)`, the kernel of `Q → Out(S)` is
`φ⁻¹(Inn(S))`. It is trivial exactly when `φ` is injective and
`φ(Q) ∩ Inn(S) = 1`. So `S ⋊_φ Q` is isolated under those hypotheses, and `Q`,
with all its finitely generated subgroups, embeds in it.
