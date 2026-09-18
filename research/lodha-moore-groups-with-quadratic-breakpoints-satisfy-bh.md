---
rg: 2
id: lodha-moore-groups-with-quadratic-breakpoints-satisfy-bh
kind: claim
title: Every finitely generated group of piecewise PGL_2(Z[1/2]) homeomorphisms of the circle embeds in a finitely presented simple group
distinct_from:
  quadratic-breakpoint-psl2z-groups-satisfy-boone-higman: that is pieces in PSL_2(Z), established through the periodic-germ hosts over V; this allows pieces with determinant a power of 2, as in the Lodha--Moore groups, and is open.
  lodha-moore-groups-embed-in-lodha-circle-group: that settles the Lodha--Moore groups, all of whose breakpoints are rational; this adds breakpoints at quadratic irrationals.
---

**OPEN.**
- Let `Λ` be the image in `PGL_2(R)` of `{A ∈ GL_2(Z[1/2]) : det A > 0}`.
- Let `PPΛ` be the group of homeomorphisms of `P^1(R)` that are piecewise in `Λ`, with finitely
  many pieces.
- **Claim:** every finitely generated subgroup of `PPΛ` embeds in a finitely presented simple
  group.

**Breakpoints are forced.** At a breakpoint `ξ`, the nontrivial element `λ_-^{-1}λ_+ ∈ Λ` fixes `ξ`.
A fixed point of a rational Möbius map is rational or a real quadratic irrational. So `PPΛ` is
piecewise `Λ` with breakpoints in `Q ∪ {∞} ∪ {quadratic irrationals}`.

**What it contains.**
- Lodha's `S`: its generators `a, b, l, s` have pieces `t+1`, elements of `PSL_2(Z)`, `2t/(1+t)`
  and `2/(3-t)`, all in `Λ`.
- The Lodha--Moore groups `G_0` and `G`: the pieces `2t/(1+t)` and `2t` are in `Λ`.
- Every piecewise `PSL_2(Z)` group.

**What is established.**
- The subgroups of `S`, by `lodha-circle-group-is-finitely-presented-and-simple`.
- The subgroups of the Cantor group `𝒢`, by `lodha-moore-groups-embed-in-lodha-circle-group`.
- The piecewise `PSL_2(Z)` groups, by `quadratic-breakpoint-psl2z-groups-satisfy-boone-higman`.

## Attempts

1. **Lodha's `S` as the base of a Belk--Hyde--Matucci germ extension** (lane `bh-linear-fields`,
   2026-09-18). The plan was to add germs at finitely many orbits `Ξ` of quadratic irrationals to
   `S`, as `periodic-germ-extensions-of-v-are-virtually-simple` does over `V`. What was found:
   - **(a) Germ groups (proved).** At a quadratic irrational `ξ`, an element of `PPΛ` fixing `ξ`
     has germ `(λ_-, λ_+)` with both `λ_± ∈ St_ξ = Stab_Λ(ξ)`.
     - `St_ξ ≅ O[1/2]^{×,N>0} / Z[1/2]^×`, where `O` is the multiplier order of `Zξ + Z` in
       `K = Q(ξ)`. The reason is that the stabilizer of `ξ` in `PGL_2(Q)` is `K^×/Q^×`, and a
       rational multiple of `α` has a matrix in `GL_2(Z[1/2])` iff `α ∈ Q^×·O[1/2]^×`.
     - By the `S`-unit theorem, `St_ξ` is abelian, of rank `s_2(K)`, the number of primes of `K`
       over 2, which is 1 or 2.
     - Elements of `S` have rational breakpoints, so their germs at `ξ` are diagonal.
   - **(b) The abelianization is infinite (proved).** Suppose `G ≤ PPΛ` is a finite germ extension
     of a base `B` whose germs at `ξ` are diagonal, and some element of `G` has a one-sided germ
     `(λ, 1)` with `λ` of infinite order. Then `(G)_ξ` is abelian, and
     `(λ_-, λ_+) ↦ λ_- λ_+^{-1}` maps `A_ξ(G) = (G)_ξ/(B)_ξ` onto a subgroup of `St_ξ` containing
     `λ`. Under BHM's standing hypotheses (no global fixed point for `B`, same orbits), their exact
     sequence `B/B' → G/G' → ⊕ A_p(G) → 0` then shows that `G/G'` is infinite.
     - The device of `periodic-germ-extensions-of-v-are-virtually-simple`, where permuting families
       makes `A_p` finite, needs germs that are not order-preserving. Circle hosts do not have them.
     - So the diagonal-transplant embedding into `G'` is unavailable over `S`. One would need `G'`
       finitely presented, which is a Σ-invariant question, or some other embedding.
   - **(c) Finiteness hypotheses (open).** The BHM finiteness theorem over `B = S` needs `Fix_S(M)`
     of type `F_n` for finite sets `M` of quadratic irrationals. Only `Stab_S(∞)` is known to be
     finitely generated (`lodha-circle-group-infinity-stabilizer-is-fg`).
   - **(d) Why `V` cannot be the base (proved).** Lodha's Lemma 2.7(1) (arXiv:1710.06220v2, p. 7)
     says a standard form without potential cancellation fails to preserve tail equivalence on a
     dense subset of its support. Elements of `V` preserve tail equivalence. So `c = y_10`, a
     standard form without potential cancellation, agrees with no element of `V` on any open subset
     of its support, and its singular set relative to `V` is infinite. Hence no group containing `c = y_10` is a finite
     germ extension of `V` in Lodha's coding. The base must already contain the percolating maps.

   **Where it stands.** A proof needs one of:
   - a Cantor-model version of `S` that contains non-order-preserving germs and is finitely
     presented (a "V-type Lodha group" `⟨V, y_10 y_110^{-1}⟩`, open);
   - or a Σ-invariant argument showing `G'` is finitely presented for the circle extension over `S`,
     together with `F_2` stabilizers `Fix_S(M)`.
