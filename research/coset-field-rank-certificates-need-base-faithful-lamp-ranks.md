---
rg: 2
id: coset-field-rank-certificates-need-base-faithful-lamp-ranks
kind: claim
title: The rank condition for the Kun-Thom coset field crossed product is a statement about the integer-lamp wreath group ring, and every site-localized rank function on that ring, including those of the marked-site stable-finiteness proofs, is blind to lamp differences
distinct_from:
  kun-thom-coset-field-crossed-product-has-the-rank-condition: that is the open rank condition for R_p itself; this reduces it to diagonal factorizations and to base-faithful Sylvester rank functions on the group ring of the integer-lamp wreath, and kills the site-localized suppliers of such functions.
  rf-lamp-permutational-wreaths-satisfy-stable-finiteness: that proves stable finiteness of the lamp group ring by marked-site separation; this shows that no Sylvester rank function on those marked-site targets sees a lamp difference, so the same targets cannot certify the rank condition after localizing to the coefficient field.
  kun-thom-binary-wreaths-stably-finite-in-characteristic-two: that is stable finiteness of the binary-lamp group ring; this concerns the integer-lamp group ring and its Ore localization, where stable finiteness is not the relevant property.
  kun-thom-coset-field-has-no-finite-field-point-models: that kills point models of the coefficient ring; this kills the other positive mechanism in the graph, site-localized models of the lamp group ring, by a different invariant (the rank of a site idempotent).
  rank-condition-rings-carry-sylvester-rank-functions: that asks whether the rank condition always yields a Sylvester rank function; this uses only the easy direction, and states the reduction so that it does not depend on that question.
---

**ESTABLISHED (unreviewed)** by [[coset-field-base-faithful-lamp-ranks-dilution-proof]].

**Setting.** Let `Γ < G` be the Kun–Thom pair, with `H = G/Γ` infinite and `p` a prime. Put:
- `L = ⊕_H Z`, the lamp group;
- `W = L ⋊ G = Z wr_H G`, the integer-lamp permutational wreath product;
- `O = F_p[L] = F_p[x_c^{±1} : c ∈ H]`, so that `F_p[W] = O ⋊ G`;
- `S = O \ {0}` and `R_p = F_p(x_c) ⋊ G`, as in `kun-thom-coset-field-crossed-product-has-the-rank-condition`.

A Sylvester matrix rank function `rk` on `F_p[W]` is **base-faithful** if `rk(s) = 1` for every `s ∈ S`.

**Theorem.**
1. **Diagonal form.** `R_p` fails the rank condition if and only if, for some `r < d`, some diagonal matrix
   `diag(s_1, ..., s_d)` with every `s_i ∈ S` factors as `A'B'` over `F_p[W]`, where `A'` has size `d x r`.
2. **Rank-function certificates.**
   - A base-faithful rank function on `F_p[W]` proves the rank condition for `R_p`.
   - Every Sylvester rank function on `R_p` restricts to a base-faithful one.
   - Being base-faithful on every finite subset of `S` is equivalent to being base-faithful on all of `S`, by
     compactness.
   - So a rank-function proof of the rank condition for `R_p` is exactly the construction of a base-faithful
     rank function on the group ring `F_p[W]`.
3. **Idempotent dilution (class kill).** Let `ψ: F_p[W] -> T` be a ring homomorphism and `rk` a Sylvester matrix
   rank function on `T`. Suppose some idempotent `e ∈ T` has infinitely many pairwise orthogonal conjugates by
   units of `T`, and `ψ(x_(c_0) - 1)` lies in the two-sided ideal `TeT` for some `c_0`. Then
   `rk(ψ(x_c - 1)) = 0` for every `c ∈ H`, so the pullback `rk ∘ ψ` is not base-faithful.
4. **Members that die.**
   - **Marked-site targets.** The marked-site tensor algebras of `rf-lamp-permutational-wreaths-satisfy-stable-finiteness`
     and `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` meet the hypothesis of item 3. Their kernels
     are finite-support matrix algebras over the infinite orbit `H`. So every Sylvester rank function on every
     such target factors through `F_p[G]`, where each lamp maps to 1.
   - **First-order jets.** The same holds for the first-order jet module `O/I^2 ≅ F_p ⊕ F_p[H]`, where `I` is the
     augmentation ideal of `O`.
   - **Why this matters.** These are the constructions that proved stable finiteness of `F_p[W]`. They separate
     the group ring, but they cannot certify its localization `R_p`.

**Invariant and dying step.** The invariant is the rank of a site idempotent. Its `G`-conjugates are pairwise
orthogonal and indexed by the infinite set `H`, so its rank is at most `1/N` for every `N`, hence 0. This is
the rank-function form of the failure of Følner normalization on the Kazhdan coset space.

**What is left** (see `## Attempts` of the target):
- **Base-faithful rank functions that are not site-localized.** The prime example is a sofic rank function.
  If `W` were sofic, the sofic rank function restricted to the amenable group `L` would be the Følner rank.
  That rank is full on the domain `O`, and so `R_p` would have the rank condition for every `p`. That step
  uses literature not in the graph.
- **Soficity of the integer-lamp wreath.** The graph records nonsoficity only for the binary lamp
  (`kun-thom-nonsofic-wreath`).
- **Linear-sofic models.** A linear-sofic model of `W` gives `rk(w - 1) = 1` for every `w ≠ 1`, which is not
  enough. On `F_p[Z^2]`, the rank over the function field of the curve `x + y + 1 = 0` has
  `rk(x^a y^b - 1) = 1` for every `(a,b) ≠ 0` and `rk(x + y + 1) = 0`.
