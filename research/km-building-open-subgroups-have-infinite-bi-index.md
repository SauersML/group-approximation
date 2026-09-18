---
rg: 2
id: km-building-open-subgroups-have-infinite-bi-index
kind: claim
title: A subgroup of a Kac--Moody group of irreducible infinite type over a finite field that contains the trace of an open subgroup of the positive completion has finite index or infinitely many double cosets
distinct_from:
  km-negative-completion-building-open-dichotomy: that transfers this dichotomy to the negative building topology through a Chevalley involution; this proves it for the positive one.
  fp-simple-type-a-actions-iff-finite-bi-index-subgroups: that turns a finitely generated proper subgroup with finitely many double cosets of a finitely presented simple group into a type (A) action and back; this shows that for Kac--Moody lattices no such subgroup can contain the trace of an open subgroup of the building completion.
  fp-simple-kac-moody-lattices-are-highly-transitive: that asks whether these groups are highly transitive; this is a no-go for one class of point stabilizers (those open in the building topology) and does not decide the question.
  km-246-completions-are-kazhdan-howe-moore-simple: that imports simplicity, (T) and Howe--Moore for the completions of type (2,4,6); this is a double-coset statement about open subgroups of any completed Kac--Moody group of irreducible infinite type over a finite field, proved from Caprace--Marquis's classification of open subgroups.
  kac-moody-lattice-confined-subgroups-are-lim-free-and-mif: that is about confined subgroups and Rybak's hyperbolic space; this is about subgroups that are open in the building topology, which are typically not confined, and about double cosets rather than limit sets.
  finite-bi-index-kazhdan-stabilizer-is-nonseparable: that shows a separable stabilizer of finite bi-index has finite index in general groups; this uses openness in a specific locally compact completion, which is neither implied by nor implies separability.
  strict-one-sided-compression-forces-infinite-bi-index: that derives infinite bi-index from a strict conjugate compression inside the ambient group; this derives it from Bruhat decomposition and Coxeter combinatorics after passing to the locally compact completion.
artifacts:
  - research/artifacts/km-building-open-subgroups-bi-index-2026-09-16.md
---

**ESTABLISHED** through `km-building-open-subgroups-bi-index-proof`. Checked once by the
swarm referee (2026-09-16: every step re-traced, the [CM] and [CR] pins re-read in TeX), not
otherwise reviewed. No novelty is claimed; it may well be folklore.

**Statement.** Let `Λ = 𝒢(F_q)` be a minimal Kac--Moody group over a finite field, with
twin root datum of Coxeter type `(W,S)`, `S` finite and `W` infinite. Let `G` be its
completion in the positive building topology (Caprace--Marquis arXiv:1108.4934v2 §4, which
is Caprace--Rémy's `\overline Λ_+`). Call `M ≤ Λ` **building-open** if `Λ ∩ V ⊆ M` for some
open subgroup `V ≤ G`. Examples are the stabilizers and pointwise fixators in `Λ` of finite
sets of chambers of the positive building, and the standard parabolics `𝓟_J`.

```text
(A)   If (W,S) is irreducible and M ≤ Λ is building-open, then
      [Λ : M] < ∞   or   |M \ Λ / M| = ∞.
(A')  If every proper parabolic W_K, K ⊊ S, is finite (which forces (W,S) irreducible, as W
      is infinite), (A) has a short proof that avoids the Coxeter step 4 below.
(A'') If N ⊴ Λ lies in the kernel Z_Λ(Λ^†) of the action on the positive building, the same
      dichotomy holds in Λ/N for every subgroup containing the image of some Λ ∩ V.
```

**Which lattices are covered.**
- **Covered.** Every quotient `Λ/Z(Λ)`, since the centre centralizes `Λ^†`. This includes the
  type `(2,4,6)` lattices `S_q = Λ_q/Z`, `q ≥ 4`, of
  `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, the explicit members of the root
  question. For `S_q`, (A') suffices, because every proper `W_K` is finite dihedral of order at
  most 12.
- **Not claimed.** Caprace--Rémy's simplicity theorem (arXiv:math/0607664v2, TeX l.132--136)
  produces `[Λ,Λ]` divided by its finite centre. When `Λ` is not perfect, that group is not a
  quotient of `Λ`, and the extension from `Λ` to the finite-index subgroup `[Λ,Λ]` was not
  worked out.

**The proof in outline.**
1. **Transfer.** The closure `O` of `M` is open, `Λ ∩ O = M`, and `|M\Λ/M| = |O\G/O|`.
2. **Classification.** By Caprace--Marquis Theorem `thm complet`, some conjugate of `O` has
   finite index in a parabolic `P_K`. If `K = S`, then `P_S = G` and `[Λ:M] < ∞`.
3. **Bruhat.** If `K ⊊ S`, the BN-pair axioms inject `W_K\W/W_K` into `P_K\G/P_K`.
4. **Coxeter.** `|W_K\W/W_K| = ∞` for every proper `K` when `(W,S)` is irreducible and `W` is
   infinite. The proof uses a strictly nested chain of roots `h^iα_s` and a root-counting
   length bound.

   For (A'), `P_K` is compact, so `O` is compact while `G` is not, and there are infinitely
   many double cosets.

**Where irreducibility is used.** Only in Step 4. For `W = W_1 × W_2` with `W_1` infinite and
`W_2` finite, and `K` the generators of `W_1`, the set `W_K\W/W_K ≅ W_2` is finite, so Step 4
fails as stated. This is not a counterexample to (A): there `P_K` has finite index in `G`.
Reducible types are not claimed. They do not matter for the target: the simplicity
theorem of Caprace--Rémy (arXiv:math/0607664v2, TeX l.135) assumes `W` irreducible, infinite and
non-affine.

**Scope.**
- **Only open closures.** Subgroups `M` whose closure in `G` is not open are not covered.
  Examples are discrete subgroups of `G`, stabilizers of ideal boundary points, and subgroups
  dense in `G`.
- **Negative building.** The analogous statement for the completion in the negative building
  topology is presumably symmetric, but is not claimed.

The consequences for multiply transitive actions are
`km-building-open-subgroups-have-infinite-ht-orbits`.
