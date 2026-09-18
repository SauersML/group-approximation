---
rg: 2
id: deligne-universal-central-extension-proof
kind: route
title: Universal central extensions are functorial and their kernels are H_2, so an injective map of perfect groups lifts injectively exactly when it is injective on H_2
target: deligne-lattice-is-universal-central-extension-for-g-ge-4
---

Item 1 is quoted in the target from the source. Items 2 and 3 are standard properties of
universal central extensions of perfect groups (Milnor, *Introduction to algebraic
K-theory*, §5; not re-read):

- (U1) a perfect group `G` has a universal central extension `G~ → G`, with kernel
  canonically `H_2(G; Z)`;
- (U2) a homomorphism `φ : G → S` of perfect groups lifts uniquely to `φ~ : G~ → S~`,
  and `φ~` restricted to the kernels is `φ_* : H_2(G) → H_2(S)`.

**Item 2.** Take `G = Sp_2g(Z)` (perfect for `g ≥ 3`) and `G~ = Γ~_g` (item 1, `g ≥ 4`).
If `φ` is injective and `φ~(x) = 1`, then `φ(image of x) = 1`, so `x` lies in the kernel
`H_2(G) = Z` of `G~ → G`. There `φ~ = φ_*`. So `ker φ~ = ker φ_*`, which is `0` iff
`φ_*` is injective iff the generator has infinite-order image, since `H_2(G) = Z`.

For the Boone--Higman consequence: `S~` is a central extension of a finitely presented
group by the finitely generated group `H_2(S)` (finitely generated as `S` is finitely
presented), hence finitely presented. It is perfect, being a universal central extension.
If `S~` embeds in a finitely presented simple group, so does `Γ~_g ⊆ S~`.

**Item 3.** If `φ = ψ ∘ ι` with `ι : G → Q`, then `φ_* = ψ_* ∘ ι_*`. If `H_2(Q)` is torsion,
`ι_*(Z)` is finite, so `φ_*` has finite image and `ker φ_*` has finite index in `Z`. For
`Q = SL_N(Z)` with `N ≥ 5`, `H_2(Q) = Z/2` by the source's page 7. (For a non-perfect `Q`
use `H_2` all the same: the factorization of `φ_*` needs only functoriality of `H_2`;
the lift `φ~` is taken to `S~`.)
