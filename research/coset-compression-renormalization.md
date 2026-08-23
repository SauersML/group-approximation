---
rg: 2
id: coset-compression-renormalization
kind: claim
title: Every one-sided compressor is a radical-renormalizing coset self-cover
distinct_from:
  wreath-compression-mf-radical: That established theorem computes the same kind of lamp radical by expansion closure and all compressor powers; this claim identifies a canonical self-cover attached to one compressor and derives the whole stable kernel by automorphization.
  sound-rule-transfinite-closure: That is an arbitrary quotient-iteration calculus; this is an explicit surjective endomorphism whose stable kernel can be calculated geometrically.
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
---

Let `Gamma<=G` have property `(T)` and let `s Gamma s^-1 <= Gamma`.  On
`X=G/Gamma`,

```text
r_s(g Gamma)=g s^-1 Gamma
```

is a well-defined `G`-equivariant surjective self-map, with
`r_s^n(g Gamma)=g s^-n Gamma`.  If

```text
Gamma_infty = union_n s^-n Gamma s^n,
```

then two sites are eventually identified by iterates of `r_s` exactly when
they have the same image in `G/Gamma_infty`.

For every countable abelian torsion lamp group `A`, the induced self-surjection

```text
R_s : A^(G/Gamma) semidirect G -> A^(G/Gamma) semidirect G
```

has `ker R_s <= Rad_MF` by pointwise compression-torsion collapse, and

```text
union_n ker(R_s^n)
 = ker( A^(G/Gamma) semidirect G
        -> A^(G/Gamma_infty) semidirect G )
 <= Rad_MF.
```

If the terminal quotient is MF, this kernel is the exact MF radical.
For a countable torsion-generated nonabelian lamp `K` and a strict compressor,
the first collapse also forces fibrewise abelianization, so the same conclusion
holds with terminal lamp `K_ab`.
