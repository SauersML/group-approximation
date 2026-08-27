---
rg: 2
id: clifford-block-amalgam-residually-finite-proof
kind: route
title: Separate the centre in a finite Clifford quotient and everything else after killing it
target: clifford-block-amalgam-residually-finite
requires: []
artifacts:
  - notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md
---

## Direct proof

Sections 7 and 8 of the artifact.  Three steps.

**(a) Free products of finitely many finite groups are residually finite.**
Let `F = A_1 * ... * A_r` with each `A_i` finite, and let `K` be the kernel of
`F -> A_1 x ... x A_r`.  That map is injective on every conjugate of every
`A_i`, so `K` meets every vertex stabilizer of the Bass--Serre tree trivially
and acts freely; hence `K` is free.  It has finite index in the finitely
generated `F`, so it is a finite-rank free group, in particular residually
finite, and (b) finishes.

**(b) Finite index inherits upward.**  A finitely generated group with a
residually finite finite-index subgroup is residually finite: pass to the
normal core `H`, which is finitely generated; an element outside `H` is
separated by `G/H`; an element `g` inside is separated by `L`, the
intersection of all index-`m` subgroups of `H` for a suitable `m`, which is
finite index (finitely many such subgroups, since each is a point stabilizer
of a homomorphism to a finite symmetric group), characteristic in `H`, hence
normal in `G`.

**(c) The two-quotient embedding.**  With `q : M_J ->> C(S_J)` the full
Clifford quotient on all `8|J|` sites (finite, and `q(zeta) != 1` there,
because `C(S_J)` has order `2^(8|J|+1)` by the ordered normal form and the
explicit cocycle model `beta(u,v) = sum_{r>s} u_r v_s` on `F_2 x F_2^S_J`),
and `r : M_J ->> M_J/<zeta>`, one has `ker r = <zeta>` by centrality and
`M_J/<zeta> = *_{i in J} (Z/2)^8` because killing the amalgamated subgroup
turns each block into `(Z/2)^8` and leaves no identification between blocks.
Then

```text
ker q ∩ ker r  =  ker q ∩ <zeta>  =  1,
```

so `(q,r)` is injective into a finite group times a group residually finite by
(a).  Subgroups of residually finite groups are residually finite. ∎

## Why this route exists alongside the older one

`literal-telescope-core-lef-proof` gets the same conclusion from
Karrass--Pietrowski--Solitar virtual freeness.  That is correct within its
hypotheses (the 2026-08-15 adversarial audit checked it after rejecting an
earlier Baumslag phrasing), but it is a literature input, and it is the LAST
one in the soficity chain.  This route replaces it with an embedding that a
formalization can follow: two explicit quotient maps and an intersection
computation, no tree of groups beyond "free action on a tree gives a free
group".

Note also what the two quotients mean.  Neither alone is faithful — `q`
collapses the block structure, `r` kills exactly the element `w = zeta` whose
survival the whole non-MF story is about — and the content is that their
kernels intersect trivially because the only thing `r` loses is central and
`q` keeps it.
