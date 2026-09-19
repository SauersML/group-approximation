---
rg: 2
id: minimal-cantor-z-crossed-products-contain-no-f2-z2
kind: claim
title: For an infinite minimal Cantor system (X,T), the algebraic crossed product LC(X,F_2) ⋊ Z contains no F_2[Z^2]; only embeddings whose image is entirely degenerate survive
distinct_from:
  spectrally-complete-tuples-bound-commutative-rank: that proves this for every commutative subalgebra containing a nondegenerate (spectrally complete) element; this is the full statement, whose only open part is subalgebras with no spectrally complete element.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that is the rank-4 question in B_Ω ⊗ L_∂; this is the rank-2 question in a Z-crossed product, the s = 1 case of the commutative-rank conjecture recorded there.
  algebraic-core-gradings-bound-homogeneous-laurent-rank: that settles the odometer (locally matrix over F_2[t^±]) and homogeneous units; this asks about all minimal systems and all elements.
---

**OPEN.** Let `(X, T)` be an infinite minimal Cantor system and `A = LC(X, F_2) ⋊_T Z`.
Then there is no injective unital algebra map `F_2[x^{±1}, y^{±1}] → A`.

**Why it matters.** This is the `s = 1` case of the commutative-rank conjecture in
`f2-z4-embeds-in-z2-sft-boundary-product-hosts`: a cocycle `Z`-valued with trivial (AF) kernel,
so rank `≤ 1`.
- A YES here, for some `X`, refutes the conjecture. It makes mechanism (ii) of that node
  (`F_2[Z^3] ⊆ B_Ω`) plausible, since `B_Ω ⊇ LC(Ω) ⋊ Z e_1`.
- A NO is the first non-graded, non-locally-matrix instance of the conjecture.

**What is known.**
- The odometer case holds, by `algebraic-core-gradings-bound-homogeneous-laurent-rank` (B).
- By `spectrally-complete-tuples-bound-commutative-rank`, the image `C` of any
  embedding has no spectrally complete element. In particular every nonscalar `z ∈ C`,
  written `z = Σ_{k=p}^{q} a_k u^k`, has `a_q ≠ 1` with `q > 0`, or `a_p ≠ 1` with `p < 0`.
- `C` is a domain, so it has no nonzero nilpotents. So `C` avoids elements like `1_U u`.
- Two commuting full-group units with disjoint supports give zero-divisors
  (`(u_g − 1)(u_h − 1) = 0`). So the obvious `Z^2 ≤ [[T]]` does not embed `F_2[Z^2]`.

**Suggested next steps.**
1. *Asymptotic degree.* Let `τ^±(z) = lim_N q^±(z^N)/N`, the top and bottom offsets of powers.
   Is `τ^+ − τ^−` a degree function on `C` whose valuation ring contradicts transcendence
   degree 2? Degeneracy makes the top coefficient of `z^N` a product of shifted `a_q`'s that
   dies by minimality, so `τ^+(z) < q(z)` exactly for the degenerate elements.
2. *Kakutani–Rokhlin reduction.* On a KR partition, `z` becomes a matrix over `F_2[t^±]`
   plus a boundary error on the tower tops. Test whether degeneracy forces the error to be
   nilpotent modulo a finite-codimension ideal.
3. *Census.* Search, by computer, for commuting pairs of degenerate elements with offsets in
   `[−2, 2]` in a Sturmian system, and check them for algebraic dependence.
