---
rg: 2
id: out-free-groups-virtually-embed-in-aut-free-groups
kind: claim
title: For every rank at least three some finite-index subgroup of Out(F_n) embeds in some Aut(F_m)
distinct_from:
  out-free-groups-satisfy-boone-higman: that is the Boone--Higman statement for Out(F_n); this is one sufficient embedding premise for it, into the hosts of BFFHZ Theorem A.
  aut-free-groups-satisfy-permutational-boone-higman: that is the known theorem that every Aut(F_m) embeds in a finitely presented simple group; this asks whether Out(F_n) virtually sits inside some Aut(F_m) at all.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**OPEN.** For every `n ≥ 3` there are a finite-index subgroup `L ≤ Out(F_n)`,
an integer `m`, and an injective homomorphism `L → Aut(F_m)`.

This premise feeds `out-fn-bh-via-virtual-embedding-in-aut-fn`.

## Attempts

1. **Lifting through a finite-index subgroup.**
   - Suppose, on a finite-index subgroup of `Out(F_n)`, each outer class is
     assigned an automorphism of a fixed finite-index `H ≤ F_n` that extends to
     a representative. By `outer-covering-lifts-are-virtual-sections` this is
     exactly a section of `Aut(F_n) → Out(F_n)` over a finite-index subgroup,
     so it gives the premise with `m = n`.
   - **Rank two.** Here the section exists. `Out(F_2) ≅ GL_2(Z)` is virtually
     free, and lifting the free generators of a free finite-index subgroup
     defines it.
   - **Rank three or more.** The literature status of virtual splitting was not
     determined in this pass. Three arXiv API queries run on MSI on 2026-09-12
     (`all:"virtually split" AND all:"free group"`, `abs:"Out(F_n)" AND abs:split`,
     `abs:"outer automorphism group" AND abs:"does not split"`) returned no paper
     on it.
2. **Restriction to a characteristic subgroup lands in Out, not Aut.**
   - Let `K ≤ F_n` be characteristic of finite index. Restriction
     `Aut(F_n) → Out(K)` has kernel the inner automorphisms by elements of `K`.
     If `φ|_K` is conjugation by `k ∈ K`, uniqueness in part (i) of
     `outer-covering-lifts-are-virtual-sections` forces `φ = c_k`.
   - So `Aut(F_n)/K` embeds in `Out(K)`. This is a finite extension of
     `Out(F_n)` by `F_n/K`, and it contains `Out(F_n)` only when that extension
     splits.
   - The result is an Out-to-Out map. Landing in `Aut(K)` instead is again a
     virtual section, as in item 1.
3. **An analogue of Aut_G(G∗F_n).** BFFHZ, arXiv:2503.21882v2 Section 4, after
   Remark 4.1: "we would want to embed it in some analog of Aut_G(G∗Fn).
   However, inner automorphisms of Fn do not interact nicely with
   G-automorphisms, so it is not clear whether this is possible." That would be
   a type (A) host containing `Out(F_n)`, not an `Aut(F_m)`, so it belongs to
   the target's Attempts.
4. **No rational cohomological obstruction to a virtual section.**
   `aut-out-free-abelianized-extension-splits-rationally`: the Fox Jacobian
   determinant restricts to `(n − 1)`·abelianization on inner automorphisms. So
   the abelianized extension class is killed by `n − 1`, and
   `Aut(F_n) → Out(F_n)` is injective on rational cohomology with coefficients
   pulled back from `Out(F_n)`.
   - **Consequence.** Transfer or cup-product arguments with such coefficients
     cannot exclude a virtual section, just as Chen--Salter needed
     nonabelian input for surfaces.
   - **Only abelian candidate left.** The integral class, of order dividing
     `n − 1`, might die on a finite-index subgroup. That was not decided.
5. **Side choice on rank-one splittings.**
   `free-splitting-fa-lifts-choose-a-side`, applicable for `n ≥ 5` via (T) for
   `Aut(F_{n−1})`: a section restricted to the automorphisms of `B` in
   `⟨p⟩ ∗ B` is either conjugate to the standard lift, or fixes exactly one
   `B`-vertex of the Bass--Serre tree. This is the analogue of Chen--Salter's
   Lemma 2.16 (the puncture lies on one side).
   - **Where it stops.** Chen--Salter conclude with an Euler-class computation
     on the handle-pushing subgroup `π1(UTΣ_p)`. The free-group partial
     conjugation subgroup is free and has no central extension, so that step has
     no direct analogue.
   - **Not ruled out.** Neither side-choice case has been excluded. Case (N)
     reduces, on inner automorphisms of `B`, to the same question one rank down.
   - **Literature.** arXiv queries on 2026-09-12 found nothing on virtual
     splitting of `Aut(F_n) → Out(F_n)`, but the search was cut short by HTTP
     429. The Laudenbach-sequence splittings (arXiv:2012.01529, 2310.13527)
     concern a different extension. Details are in
     `research/artifacts/bh-aut-out-virtual-section-2026-09-12.md`.
