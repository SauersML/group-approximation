# STW Problem XCIX: prime dimension-drop modulus audit (2026-08-30)

## Existing-graph comparison

All XCIX claims and routes were checked before adding this node.  The
existing global scalar `kappa_Z` uses approximately central embeddings of
the entire Jiang--Su algebra.  Transport relies on the approximately inner
half-flip theorem and costs `304 sqrt(gamma)+2 gamma`.  The new scalar uses
only fixed finite generating sets of the prime dimension-drop algebras
`I_(k,k+1)`.  Its zero-set identification imports the exact local
dimension-drop criterion
`stw99-xciv-separable-zstability-iff-local-prime-dimension-drops`, while its
transport uses nuclear dimension one.  The resulting leading constant is
`160`, so this is not a renaming of the existing modulus.

The fixed-window collapse theorem uses the first `k` elements of one dense
sequence in `Z` and does not identify a finite presentation witnessing each
window.  Here each block has a fixed finite generating set and every target
map is an exact homomorphism.  The nuclear and either-side-nuclear positive
radii produce isomorphisms of the whole close algebras; the new result
assumes neither algebra is nuclear and does not assert an isomorphism.

## Imported quantitative theorem and constants

Christensen--Sinclair--Smith--White--Winter,
[*Perturbations of nuclear C\*-algebras*](https://arxiv.org/abs/0910.4953),
Theorem 6.10, says that if `D subset_gamma B`, `D` is separable with
`dim_nuc(D)<=n`, and

```text
eta=2(n+1)(2 gamma+gamma^2)(2+2 gamma+gamma^2)<1/210000,
```

then on each finite subset of `D_1` there is an actual embedding `D->B`
within `20 sqrt(eta)` of the inclusion.  For `n=1` this is the `eta` in the
claim.  At `gamma<1/5670000`, the elementary estimate `eta<27 gamma` proves
the strict theorem hypothesis.  The commutator perturbation contributes
twice the embedding error and twice the ambient-element error, giving

```text
40 sqrt(eta)+2 gamma
 =80 sqrt((2 gamma+gamma^2)(2+2 gamma+gamma^2))+2 gamma.
```

No rounding is hidden in this expression.

## Map and unit audit

A unital homomorphism `I_k->A` can have a kernel because `I_k` is not simple.
The proof therefore applies Theorem 6.10 to its image `D`, not to `I_k`.
Nuclear dimension passes to quotients, so `dim_nuc(D)<=1`.  The theorem gives
an actual embedding of `D`; composition with the quotient map gives the
required exact homomorphism from `I_k`.

The close algebras are required to have a common unit.  Including `1_D` in
the controlled finite set puts the image support projection within
`20 sqrt(eta)<1` of that unit, forcing equality.  Without this step the
transported homomorphism need not be unital.  Kadison--Kastler closeness is
used only to choose nearby contractions and to establish the one-sided near
inclusion `D subset_gamma B`; those choices are never assembled into a map.

## Open boundary

For separable unital algebras, the finite-block modulus vanishes exactly at
`Z`-stability and is Holder-continuous in the stated range once all prime
blocks embed.  Holder continuity does not make its zero set open.  A
vanishing-distance XCIX counterexample sequence would have positive defects
tending to zero at the new rate, so the unrestricted root remains open.
