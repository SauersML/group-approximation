---
rg: 2
id: kazhdan-regular-block-periodizations-of-mapping-tori-are-finite
kind: claim
title: A block-monomial model of a Kazhdan mapping torus built from regular representations of finite quotients, with wrap defect below min(kappa/sqrt2, sqrt3/L), is a genuine representation through a finite quotient, so it is trivial on a quotientless kernel in every dimension
distinct_from:
  quotient-permuting-and-ambient-inner-mapping-tori-are-lef: that proves LEF when the automorphism exactly permutes a family of finite quotients of a mother group; this proves that an operator-norm approximate permutation of regular finite-quotient blocks is automatically exact, uniformly in dimension, so no approximate version of that construction can escape it.
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that records that the periodization construction dies at the wrap for one natural choice of wrap; this proves the wrap defect is at least min(kappa/sqrt2, sqrt3/L) for every wrap unitary, every block permutation and every block size.
  twisted-lef-tower-order-budget-kills-compression-defects: that uses Lagrange along phi-twisted LEF layers to kill compression certificates and uses no (T); this uses (T) of a finitely presented cover through the Hilbert--Schmidt conjugation representation and a Mirsky rank count, and bounds operator-norm models of the whole mapping torus, not certificates.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that builds a finite von Neumann model nontrivial on the kernel with a Folner wrap of trace 1/N; this shows that the operator-norm analogue of that wrap, with regular blocks, costs a constant independent of N.
  compression-defect-dies-in-finite-dimensions: that kills the defect in genuine finite-dimensional representations; this shows that a whole class of approximate representations is genuine.
artifacts:
  - research/kazhdan-regular-block-periodizations-of-mapping-tori-are-finite-proof.md
  - research/fpbs-shalom-property-t-is-open.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
---

**ESTABLISHED.** Proof: `kazhdan-regular-block-periodizations-of-mapping-tori-are-finite-proof`.
It is elementary, apart from the imported openness of property (T) (Shalom) and the
Eckart--Young--Mirsky inequality.

## Setting

Let `K` be a finitely generated Kazhdan group, `φ ∈ Aut(K)`, and suppose that
`G = K ⋊_φ Z` is finitely presented. By `fp-mapping-torus-iff-finite-automorphic-presentation`
and `fpbs-shalom-property-t-is-open`, `G` has a presentation

```text
G = < S, t | R_0 ,  t s t^-1 = w_s  (s in S) >,     R_0 ⊂ F_S finite,  w_s ∈ F_S,
```

in which `K~ = <S | R_0>` has property (T). (Adding finitely many further relators of `K` to `R_0`
keeps this a presentation of `G`.) Let `κ > 0` be a Kazhdan constant of `K~` for `S`, and let `L`
be the maximal length of a relator in `R_0`. Put

```text
ε_0 = min( κ/√2 , √3/L ).
```

## Regular block models

A **regular block model** of `G` consists of the following data.

- A finite index set `I`, and for each `i` a finite group `Π_i` and a homomorphism
  `θ_i : K~ -> Π_i`.
- The space `H = ⊕_i ℓ²(Π_i)`, with `U(s) = ⊕_i λ_(Π_i)(θ_i(s))` for `s` in `S`.
- A permutation `τ` of `I` with `|Π_(τ i)| = |Π_i|`, and unitaries
  `V_i : ℓ²(Π_i) -> ℓ²(Π_(τ i))`. Here `T = ⊕_i V_i` carries block `i` onto block `τ i`.

Its **defect** is `δ = max_(s in S) ‖T U(s) T* − U(w_s)‖` (operator norm). Here `U(w_s)` is the word
`w_s` evaluated at the `U(s)`, and the relators `R_0` hold exactly by construction.

This class contains every periodized twisted LEF tower
`U = ⊕_(m<p) λ(ι ∘ φ^(-m))` with the cyclic shift and an arbitrary wrap unitary. It also contains
direct sums of such towers, arbitrary multiplicities and arbitrary block permutations. Blocks
of the form `λ_Π ∘ θ` with `θ` not onto are allowed, and these give multiples of regular
representations of quotients.

## Statement

**(RB1) Kernel rigidity.** Let `Π, Π'` be finite groups of the same order `n`, and let
`θ : K~ -> Π`, `θ' : K~ -> Π'` be homomorphisms. Suppose a unitary
`V : ℓ²(Π) -> ℓ²(Π')` satisfies `‖V λ(θ(s)) V* − λ'(θ'(s))‖ < κ/√2` for all `s` in `S`.
Then `ker θ = ker θ'`. The bound does not depend on `n`.

**(RB2) Regular block models below `ε_0` are finite.** Let a regular block model have defect
`δ < ε_0`, and put `H_i = θ_i(K~)`. Then:

- there are isomorphisms `α_i : H_i -> H_(τ i)` with `α_i ∘ θ_i = θ_(τ i) ∘ ŵ` on `F_S`, where
  `ŵ(s) = w_s`;
- `s ↦ (θ_i(s))_i` and `t ↦ τ^` define a homomorphism `Ψ : G -> Q = (∏_i H_i) ⋊ <τ^>` onto a
  finite group, where `(τ^ x)_(τ i) = α_i(x_i)`;
- `U(k) = ⊕_i λ(Ψ(k)_i)` for every `k` in `K`.

So `U|_K` is a genuine representation of `G` through a finite quotient.

**(RB3) Quotientless kernels.** If `K` has no nontrivial finite quotient, then every regular block
model of `G` with defect `δ < ε_0` has `U(s) = 1` for all `s`, in every dimension. By
`mapping-torus-mf-radical-lies-in-finite-residual`, this applies to every witness of (LK3) in
`torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`, to every witness of
`mf-kazhdan-quotientless-mapping-torus-exact-radical`, and to every Kazhdan-kernel witness of
`torsion-free-sofic-exact-mf-radical-over-z`.

## What this kills

**The class.** Every attempt to show that such a mapping torus is MF, or more generally to find
operator-norm models of it that are faithful on the kernel, by periodizing regular representations
of finite quotients of `K` along `φ`. This includes towers, sums of towers, multiplicities, any wrap
unitary, any block permutation and any block size. It is the operator-norm form of the construction
behind every known sofic model of LEF-by-`Z` groups.

**The invariant.** The invariant is the kernel `ker θ_i ⊴ K~` of each block. Hilbert--Schmidt
conjugation is a unitary representation of `K~`, so (T) moves the wrap unitary within
`(δ/κ)·‖V‖_2` of an exact intertwiner. The Mirsky rank count then shows that an intertwiner between
regular representations with different kernels has rank at most `n/2`. The inequality
`n − n/2 < (δ/κ)² n` fails once `δ < κ/√2`.

**Where every member dies.** At the wrap, the block kernels are forced to be exactly permuted by
`φ`. That makes the model a representation of `G` through a finite quotient, and a quotientless
kernel dies there. So Attempt 1's "the wrap cannot occur" becomes a uniform operator-norm gap:
every such model of a witness has wrap defect at least `ε_0` in every dimension.

**What survives.** Any MF model of a witness that is faithful on `K`, if it exists, must use one of
the following:

- blocks that are not multiples of regular representations of finite quotients, such as
  permutation representations `ℓ²(Π/Λ)` with `Λ` not normal. Gassmann-equivalent subgroups give
  isomorphic permutation representations with different stabilizers, so (RB1) genuinely fails
  there;
- blocks with infinite image;
- a `T` that is not block-monomial.

Conversely, for the construction of a witness this is positive evidence. (LK3) holds automatically
on the whole regular-block class, with an explicit dimension-free constant.
