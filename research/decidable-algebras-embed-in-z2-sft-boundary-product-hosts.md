---
rg: 2
id: decidable-algebras-embed-in-z2-sft-boundary-product-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds unitally in B_Ω ⊗ L_∂ for some free minimal Z^2-SFT Ω with finitely presented crossed product
distinct_from:
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that allows any torsion-free Farrell–Jones acting group and any Cantor space; this fixes the acting group Z^2 × F_d and the space Ω × ∂F_d with Ω a free minimal Z^2-SFT, and implies that claim.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one quantum rigid free minimal Z^2-SFT over some field; this asks, over F_2, for a family of them whose boundary tensors contain every decidable group algebra.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem.
Then there are:
- a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω = LC(Ω, F_2) ⋊ Z^2` finitely
  presented;
- some `d >= 2`;
- a unital embedding `F_2[G] -> B_Ω ⊗ (LC(∂F_d, F_2) ⋊ F_d)`.

**Why it matters.** Through
`cantor-crossed-hosts-are-closed-under-boundary-products`, it implies
`decidable-group-algebras-have-fp-cantor-crossed-hosts` (route
`cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`), and hence
`boone-higman-conjecture` along the graph's chain.

Unlike the bare `Z^2` case (Attempt 2 on the target), a positive answer does
not make `G` linear sofic through a rank model, because the host has none.

**Prerequisites that can fail separately** (artifact Section 4):
- (Q) Existence of one quantum rigid free minimal `Z^2`-SFT over `F_2`. This is the
  `F_2` form of `free-minimal-z2-sft-is-quantum-rigid`.
- (H) The SFTs used must have no uniform recursive language bound. That this is
  necessary is only sketched: it is the table argument of Attempt 6 on the
  target, run over `Z^2 × F_d`.
  - Without freeness and rigidity, hard minimal SFTs exist
    (`minimal-z2-sfts-have-no-uniform-language-time-bound`).
- (E) The embedding.

## Attempts

1. **Entropy-measure transplant: a commutative-rank bound for `F_2[Z^4]` (swarm-0917-w12-w12-z-pull, 2026-09-18). OPEN; dies at inhomogeneous units.**
   - **Test case.** `F_2[Z^4]` is decidable, so (E) needs `F_2[Z^4] ⊆ B_Ω ⊗ L_∂`.
   - **Heuristic for NO.** The host is a `Z^3`-graded algebra (lattice plus gauge)
     with algebraic core. That suggests commutative rank `<= 3`, just as the GK
     dimension of `LC(X) ⋊ Z^s` is bounded by `s` plus the complexity exponent.
   - **Established pieces** (`algebraic-core-gradings-bound-homogeneous-laurent-rank`):
     - (A) Units homogeneous for any rank `<= 3` grading with algebraic core never
       carry `F_2[Z^4]`. This covers the lattice-plus-gauge grading.
     - (A) Gauge-homogeneous units of any corner of `L_∂` never carry `F_2[Z^2]`.
     - (B) Subalgebras that are locally matrices over commutative algebras of local
       dimension `<= 3` never contain `F_2[Z^4]`.
     - So every YES construction must be inhomogeneous in every such grading and
       locally non-PI.
   - **Where it dies.** Four independent reasons:
     1. For an inhomogeneous unit, leading terms are not multiplicative, because
        the host has zero divisors in every degree.
     2. With dense periodic points, `LC(X) ⋊ Z` embeds only in an *infinite*
        product `∏ M_n(F[t^±])`. The domain-into-one-factor step fails there.
     3. The orbit band-matrix count bounds `dim A_{<=k} ~ k^2` only by
        `p(Ck)·Ck`. That bound is vacuous at complexity `p(n) >= n+1`, and
        exponential for `L_∂`.
     4. Growth, GK dimension and entropy do not see commutative rank inside `L_∂`,
        which contains free algebras.
   - **What would settle the fork.**
     - **NO:** a rank bound for commutative domains in `L(E)` itself, meaning no
       `F[x^±, y^±]` in any corner of `L_2`. This needs a genuinely inhomogeneous
       argument, for example through centralisers in `L(E)`.
       - Unchecked observation: for `h ∈ F_d` not a proper power, the centraliser
         of `h` in `L_∂` looks like `F[h^±]`. The reason is that `h`-invariant
         locally constant functions on `∂F_d` are constant (north-south dynamics).
     - **YES:** any embedding `L_2 ⊗ L_2 -> L_2`, even into a corner. It would carry
       the commuting isometries `s_0 ⊗ 1`, `1 ⊗ s_0`, which generate `F[x,y]`.
       - Brownlowe–Sørensen (arXiv:1603.03618) exclude this only for unital
         `*`-maps.
