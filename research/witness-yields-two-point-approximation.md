---
rg: 2
id: witness-yields-two-point-approximation
kind: route
title: A Hilbert embeddable witness yields a two-point approximation
target: two-point-orbit-approximation
requires: [hilbert-embeddable-witness-for-kun-thom-wreath]
artifacts:
  - notes/TRUE_LAMP_CHARACTER_ORBIT_SEPARATION.md
  - notes/TRUE_HILBERT_EMBEDDABLE_IS_REPRESENTATION_REALIZED.md
---

# A Hilbert embeddable witness yields a two-point approximation

The direction that makes `two-point-orbit-approximation` load-bearing: it is a
**necessary condition** for a witness, so refuting it closes the lane. The
route is recorded in this direction and not the other; nothing here claims that
a two-point approximation suffices.

Let `K = L ⋊ A` be a witness group with `L = (ℤ/2)^Sites` the lamps and `A` the
acting part, and let `ρ` be the realizing representation supplied by
`hilbert-embeddable-is-representation-realized`. Decompose `ρ` into
irreducibles; by `lamp-character-orbit-separation` only the constituents
nontrivial on `L` can separate the mark, and by Mackey's construction for a
semidirect product with abelian normal subgroup each such constituent is
induced from a lamp character `θ` with `A`-orbit `𝒪 ≅ A/A_θ`, of degree
`|𝒪|·ψ(1)`.

**The defect condition becomes a Hamming condition on `𝒪`.** For `g` in the
acting part, the induced-character formula gives
`χ(g) = Σ_{aA_θ : a⁻¹ga ∈ A_θ} ψ(a⁻¹ga)`, and the cosets `aA_θ` with
`a⁻¹ga ∈ A_θ` are exactly the points of `𝒪` fixed by `g`. Hence

```text
|φ(g)| = |χ(g)|/χ(1) ≤ |Fix_𝒪(g)| / |𝒪|.
```

So `φ(g) ≈ 1` — small defect at `g` — forces `g` to fix all but an `ε`-fraction
of `𝒪`. Applied to the multiplicative defects of the witness, this says the
composite `Φ → K → A → Sym(𝒪)` is `(F,ε)`-multiplicative in the normalized
Hamming metric: a genuine approximate action on a finite set.

**The separation condition becomes two-point resolution.** By
`lamp-character-orbit-separation`, the mark `w = a_p a_q` has normalized
separation `2·|{θ' ∈ 𝒪 : |supp(θ') ∩ {p,q}| odd}| / |𝒪|`. Separation bounded
below therefore forces a constant fraction of `𝒪` to contain exactly one of
`p`, `q`; taking `B = {0,1}` and `j_{θ'}(x) = [x ∈ supp(θ')]` on that fraction
gives `j_{θ'}(p) ≠ j_{θ'}(q)`, and the `A`-equivariance of the orbit gives the
covariance clause. That is the data of `two-point-orbit-approximation`.

## The step this route commits to, stated plainly

The equivariance clause transports along `𝒪` because `𝒪` is an `A`-set of
lamp characters and the labels `j` are read off supports; the density condition
comes from the constant fraction above after the standard shrinking
(Alekseev–Bradford Lemma 4.19) to make the `F`-translates stay inside the good
set. `requires` is the witness claim alone, which is the honest accounting:
everything else here is computation from the two cited established claims.

## What is NOT claimed

That a two-point approximation suffices for a witness. The converse needs the
finite group and the representation to be built from the set data, and the
resolution question — whether an approximate action fixing most of an orbit of
**subsets** forces an approximate action on the **sites** — is open and is
tracked separately. Without it, refuting `two-point-orbit-approximation` closes
the lane but establishing it does not open it.
