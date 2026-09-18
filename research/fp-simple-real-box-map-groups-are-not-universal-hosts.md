---
rg: 2
id: fp-simple-real-box-map-groups-are-not-universal-hosts
kind: claim
title: Finitely presented groups of box-exchange maps of [0,1)^n (as nV) with arbitrary real data specialize to algebraic data, so their finitely generated simple subgroups have exponential-time word problems and no class of such finitely presented simple groups, over all n and all real data, is a universal Boone--Higman host
requires:
  - fp-piecewise-projective-groups-specialize-to-algebraic-data
  - complexity-bounded-host-classes-are-not-universal
distinct_from:
  fp-piecewise-projective-groups-specialize-to-algebraic-data: that is the one-dimensional piecewise-projective case, with a polynomial bound; this adds box maps in every finite dimension (Brin--Thompson nV and its real-parameter relatives), with an exponential bound, and draws the non-universality consequence for the whole class.
  complexity-bounded-host-classes-are-not-universal: that is the general principle that a host class with one recursive bound is not universal; this proves that the class of all finitely presented simple groups of finite-dimensional real box maps or one-dimensional piecewise-projective maps has such a bound, whatever the real parameters.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the open root; this shows no finite-dimensional real-geometric host of these kinds can witness it.
---

**ESTABLISHED** (lane proof, elementary given Tarski--Seidenberg; not reviewed). No priority is
claimed. That `nV` itself has coNP word problem is Birget's theorem. The new point is that
arbitrary real parameters do not raise the bound for finitely presented groups.

## Setting

Let `n >= 1` and `X_n = [0,1)^n`. A *box map* is a bijection of `X_n` with a finite partition into
half-open boxes `∏_i [a_i, b_i)`, `a_i < b_i`. On each box it is `x ↦ π(s ⊙ x + t)`: a positive
diagonal scaling `s`, a translation `t`, then a coordinate permutation `π`, onto a half-open box.
The *data* are the endpoints and the entries of `s` and `t`. Examples:
- Brin--Thompson `nV` (dyadic data);
- Stein-type groups in dimension `n`;
- for `n = 1`, all PL maps of Thompson `V`-type with arbitrary slopes.

`Box_n(K)` is the group of box maps with data in `K ⊆ R`.

## Statement

Let `G` be finitely presented with a faithful action on `X_n` by box maps with arbitrary real data.
1. **Specialization.** For every finite `F ⊂ G ∖ {1}` there is a homomorphism `G → Box_n(K)`, with
   `K` a real number field, that is nontrivial on `F`.
2. `G` has solvable word problem.
3. Every finitely generated simple subgroup of `G` embeds in `Box_n(K)` for a real number field `K`.
   Its word problem is decidable in time `C·2^{C·l}`.
4. **Non-universality.** Let `𝒦` be the class of finitely presented simple groups that act faithfully
   either by box maps on some `X_n` (any `n`, any real data) or by one-dimensional piecewise-projective
   maps as in `fp-piecewise-projective-groups-specialize-to-algebraic-data`. Then some 2-generated
   group with solvable word problem embeds in no member of `𝒦`.

## Proof

**Items 1–2.** Repeat the proof of `fp-piecewise-projective-groups-specialize-to-algebraic-data`
word for word, with three changes.
- The data of the generators, for a fixed combinatorial type, form a point of a semialgebraic set
  `Θ` defined over `Q`, whose points are the representations satisfying the relators.
- Real algebraic points are dense in `Θ` by Tarski transfer.
- For nontriviality, the pieces of a product of box maps are intersections of half-open boxes with
  preimages of half-open boxes. So they are half-open boxes, and each nonempty one has interior. A
  nonidentity map `x ↦ π(s ⊙ x + t)` fixes only an affine subspace of such a box, so a nontrivial
  element moves every point of some open set. Choose a point there whose partial orbit avoids all
  piece boundaries. Its image then depends continuously on the data.

**Item 3.** Simplicity turns item 1 into an embedding, as in the one-dimensional node. Over
`K = Q(β)`, a word of length `l` gives at most `N^l` pieces, where `N` bounds the pieces of the
generators.
- **Sizes.** Coordinates transform independently, up to permutation, by one-variable affine maps with
  fixed coefficients in `K`. So every endpoint, scaling and translation of a piece has bit-size `O(l)`.
- **Comparisons.** Each comparison is a sign in `K` of bit-size `O(l)`, decidable in polynomial time
  (norm bound, as there).
- **Identity.** The word is trivial iff every nonempty piece has `s = 1`, `t = 0` and `π = id`.

The total time is `2^{O(l)}`.

**Item 4.** Every member of `𝒦` is its own finitely generated simple subgroup. So by item 3, or by
item 3 of the one-dimensional node, its word problem runs in time `C·T(C·l) + C` with `T(l) = 2^l`.
Now apply `complexity-bounded-host-classes-are-not-universal`. ∎

## Lesson for general BH

- **Real parameters carry no complexity.** Finite presentation together with a tame, bounded-dimension
  action lets every continuous parameter be specialized to algebraic numbers without losing any
  finite set of nontrivial elements, a real-closed-field Mal'cev argument. A host's word problem is
  then governed by combinatorial growth: linear in dimension one, exponential for boxes. So
  finite-dimensional real-geometric hosts are capped, and the Birget root (a necessary consequence of
  BH) can never be met by them.
- **Where a universal host must live.** A universal construction has to go symbolic and
  infinite-dimensional, where the input's algorithm can be simulated in the combinatorics. Examples:
  twisted Brin--Thompson `SV_G` over infinite `S`, or Röver--Nekrashevych groups over self-similar
  actors. Tuning real slopes, breakpoints or Möbius data can never do it.
- **Quick test for a proposed host.** Does it act faithfully by finitely many tame pieces on a
  finite-dimensional real domain? If so, it is capped.
