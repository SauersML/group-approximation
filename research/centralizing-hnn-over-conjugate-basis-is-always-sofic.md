---
rg: 2
id: centralizing-hnn-over-conjugate-basis-is-always-sofic
kind: claim
title: The centralizing HNN extensions over conjugates of one generator are sofic for every index set, residually finite or not
distinct_from:
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that decides residual finiteness of the same groups by a closure criterion; this shows soficity never fails on the family, so the family separates residual finiteness from soficity uniformly.
  sofic-safe-finite-presentation-compiler: that needs soficity of a centralizing HNN extension over a Mikhailova-type subgroup; this proves it for the conjugate-basis subgroups by exhibiting a second infinite-cyclic quotient with a right-angled Artin kernel, a trick recorded here precisely because the compiler's groups do not visibly admit it.
---

ESTABLISHED.  For every `J <= Z` the group

```text
H_J = < a, b, s | [s, b^j a b^-j] = 1,  j in J >
```

of [[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]] is
sofic.  Since `H_J` is residually finite iff `J` is profinitely closed in
`Z`, the family `{H_J}` realizes both a residually finite and a
non-residually-finite sofic group by varying one index set, with three
generators throughout.

**Mechanism.**  `H_J` has two infinite cyclic quotients.  Killing `s`
exhibits it as `F(a,b) *_{A_J} (A_J x Z)`, an amalgam over a non-amenable
subgroup, which is the presentation the residual-finiteness analysis uses
and which the sofic closure theorems cannot handle.  Killing `a` and `s`
instead (`b |-> 1`) exhibits it as `N_J x| Z` where `N_J` is the
right-angled Artin group on the bipartite graph with vertices
`{a_i, s_k : i, k in Z}` and edges `a_i -- s_k` iff `i - k in J`; the shift
acts by a graph automorphism.  Right-angled Artin groups are residually
finite, hence sofic, and extensions of sofic groups by amenable groups are
sofic (Elek--Szabo, *On sofic groups*, J. Group Theory 9 (2006), Thm. 1).

**Why it matters for the compiler.**  The MF-safe compiler's first rope
`Gamma_e = <K_e, v | [v, L_e] = 1>` has the same amalgam shape, and by the
same Reidemeister--Schreier computation its kernel under `v |-> 1` is the
iterated double of `K_e` over `L_e`, an amalgam over a non-amenable
subgroup.  What makes `H_J` tractable is the *other* quotient, whose kernel
is a right-angled Artin group because `A_J` is spanned by part of a free
basis of a normal subgroup of the base.  A sofic-safe compiler would need
a benign witness `(K_e, L_e)` admitting an analogous second splitting.
