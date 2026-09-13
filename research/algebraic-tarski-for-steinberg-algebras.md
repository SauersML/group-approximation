---
rg: 2
id: algebraic-tarski-for-steinberg-algebras
kind: claim
title: For a minimal ample groupoid, a rank function on its Steinberg algebra forces stable finiteness, which forces complete non-paradoxicality, which is an invariant probability measure
distinct_from:
  rainone-sims-type-semigroup-dichotomy: that is the C*-algebra statement, where a faithful trace and stable finiteness of C*_r(G) are equivalent to complete non-paradoxicality for minimal G; this is the purely algebraic chain for the Steinberg algebra A_k(G) over an arbitrary countable field, where only one direction is known outside characteristic zero.
  simple-ring-stably-finite-iff-unit-not-paradoxical: that is the ring-level equivalence between stable finiteness and non-paradoxicality of [R] in V(R); this transfers the paradox question down to the type semigroup of the groupoid, which does not mention the field, and adds the rank-function end of the chain.
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that is the contrapositive branch, deducing a properly infinite multiple of the unit and the failure of MF quotients from the absence of invariant measures; this is the measure branch, which produces stable finiteness and rank functions.
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

**ESTABLISHED** (unreviewed; proof route `algebraic-tarski-for-steinberg-algebras-proof`).

Let `k` be a countable field, `𝒢` a Hausdorff ample second countable **minimal** groupoid with compact
unit space `X`, `R = A_k(𝒢)` the Steinberg algebra, `S(𝒢)` the type semigroup and `θ = [X]`. Then

1. if `R` carries a nonzero Sylvester matrix rank function, `R` is stably finite;
2. if `R` is stably finite, `θ` is completely non-paradoxical;
3. `θ` is completely non-paradoxical **iff** `X` carries a `𝒢`-invariant Borel probability measure.

If `𝒢` is also effective, `R` is simple, and then every nonzero Sylvester matrix rank function on `R`
is automatically faithful.

**What this is and is not.**
- Step 2 is the transfer from the groupoid to the ring. The ring-level equivalence between stable
  finiteness and non-paradoxicality of `[R]` in `V(R)` is `simple-ring-stably-finite-iff-unit-not-paradoxical`
  (lane `un-middle`), which this claim cites rather than reproves. The composite reads: `θ`
  paradoxical in `S(𝒢)` ⟹ `[1]` paradoxical in `V(R)` ⟺ `R` not stably finite.
- Step 1 is a strict step above a state on `V(R)`. A state measures finitely generated projective
  modules; a Sylvester matrix rank function measures every matrix, singular ones included. The two
  agree over von Neumann regular rings, and the algebras here are not regular.
- The chain is **not** known to reverse outside characteristic zero. For `k ⊆ ℂ` it does, by
  `invariant-measure-gives-rank-function-in-char-zero`, and then all four conditions are equivalent.
  In characteristic `p` the missing arrow is
  `invariant-measure-gives-rank-function-any-field`, which is open and contains Kaplansky stable
  finiteness (`measure-side-stable-finiteness-contains-char-p-kaplansky`).

**Field-independence.** `S(𝒢)` does not mention `k`. So the branch a groupoid falls into is a property
of `𝒢` alone, while its consequences for `R` are field-dependent. This is the structural reason the
non-MF paper (over `F_2`) and the Pestov 9.1 answer (over `F_q`) are two branches of one groupoid
statement. Whether the ring-level paradox conversely descends to `S(𝒢)` is the open claim
`type-semigroup-reflects-paradox-of-steinberg-algebra`.

**Model tests.**
- Cuntz groupoid: `2θ = θ`, no invariant measure, `L_k(1,2)` not stably finite. Consistent, and the
  chain correctly refuses to give a rank function.
- Minimal subshift over `Z`: an invariant measure exists, `LC(X,F_q)⋊Z` is stably finite, and a
  faithful rank function exists by `cantor-z-crossed-product-embeds-in-continuous-factor`. All four
  conditions hold, as they must for the Pestov 9.1 group to be LEF.

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: Lemma 2.1 (the rank-zero set is a two-sided ideal of each `M_n(R)`), Lemma 2.2 (`rk(e)+rk(1−e)=n`, since `diag(e,1−e)` is equivalent to `I_n ⊕ 0` by invertible matrices), Theorem 2.3 (padding to `M_(n+1)(R)`), Theorem 2.4 (minimality gives `θ ≤ m[U]`; ABBL extension), and that `ι : S(𝒢) → V(R)` respects the ABBL relations. Rainone–Sims Thm 6.2 (TeX label `Tarski`) and ABBL Lemma 2.3 (label `lem:RS-forgroupoids`) match the arXiv TeX sources verbatim. No established node conflicts. Details: `research/artifacts/un-review3-2026-09-13-part1.md` §1.
