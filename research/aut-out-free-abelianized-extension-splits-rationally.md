---
rg: 2
id: aut-out-free-abelianized-extension-splits-rationally
kind: claim
title: The abelianized extension of Out(F_n) by H_1(F_n) is killed by n minus one, so Aut to Out is injective on rational cohomology
distinct_from:
  outer-covering-lifts-are-virtual-sections: that identifies covering-lift constructions with virtual sections of Aut(F_n) to Out(F_n); this shows rational cohomology with coefficients pulled back from Out(F_n) can never obstruct such a section.
  birman-exact-sequence-does-not-virtually-split: that is the Chen--Salter theorem excluding virtual sections of the surface Birman sequence by a nonabelian argument; this is the free-group fact that the abelian level carries no rational obstruction at all.
artifacts:
  - research/artifacts/bh-aut-out-virtual-section-2026-09-12.md
---

**ESTABLISHED.** No novelty is claimed. The Fox determinant cocycle is classical,
and the torsion order matches known twisted homology of `Aut(F_n)`, which was
not re-read from source.

Let `n ≥ 2`, `H = H_1(F_n; Z)`, and `π: Aut(F_n) → Out(F_n)`.

1. **Cocycle.** The unit part of the abelianized Fox Jacobian determinant,
   `det(∂φ(x_k)/∂x_i)^{ab} = ±h(φ)`, defines a crossed homomorphism
   `h: Aut(F_n) → H` with `h(ι_g) = (n − 1)[g]` for every inner automorphism
   `ι_g`.
2. **Torsion.** The extension `1 → H → Aut(F_n)/[Inn, Inn] → Out(F_n) → 1` has
   class `c ∈ H²(Out(F_n); H)` with `(n − 1)·c = 0`.
3. **Injectivity.** For every `Q[Out(F_n)]`-module `M` and every `k`, the map
   `π^*: H^k(Out(F_n); M) → H^k(Aut(F_n); M)` is injective.

**What this rules out.** A section over a finite-index `Γ` forces `π^*` to be
injective on such coefficients, since `res_Γ = s^*π^*` and `res_Γ` is injective
by transfer. That condition always holds. So no rational cohomological or
transfer argument with coefficients pulled back from `Out(F_n)` can exclude a
virtual section. An exclusion must use nonabelian structure, coefficients
nontrivial on `F_n`, or torsion. This mirrors the surface case, where Morita's
crossed homomorphism restricts to `(2 − 2g)`·abelianization and Chen--Salter
need geometric input.

The proof is `aut-out-free-abelianized-extension-proof`.
