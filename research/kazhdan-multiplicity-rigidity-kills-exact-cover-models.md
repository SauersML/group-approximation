---
rg: 2
id: kazhdan-multiplicity-rigidity-kills-exact-cover-models
kind: claim
title: Operator-norm close finite-dimensional representations of a Kazhdan group are unitarily equivalent, so every model of a finitely presented Kazhdan mapping torus whose kernel part lifts to exact representations of a finite-radius cover is a genuine representation, and is trivial on a quotientless kernel for any wrap
distinct_from:
  kazhdan-regular-block-periodizations-of-mapping-tori-are-finite: that needs regular blocks of finite quotients and a block-monomial wrap, and compares block kernels by an HS rank count; this compares multiplicities by operator-norm Kazhdan projections, so it allows any wrap unitary, any blocks (permutation, Gassmann, infinite image) and answers the mismatch question left in its section 4.
  irreducible-kazhdan-representations-have-uniform-hs-rigidity: that corrects an HS-almost representation near one irreducible representation; this compares two exact, possibly reducible, representations in operator norm and concludes equivalence with no correction step.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that builds a finite von Neumann (tracial) model nontrivial on the kernel; this is the operator-norm statement that no exact-cover model can do so, which is consistent because the tracial wrap is not operator-norm small.
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that is the open radical equation (XMF); this proves it on the class of exact-cover models and reformulates it as relative liftability.
  lef-implies-operator-mf: that builds the MF models of a LEF kernel from local embeddings; this shows none of those models, with any representations of the local groups, extends to the mapping torus.
artifacts:
  - research/kazhdan-multiplicity-rigidity-kills-exact-cover-models-proof.md
  - research/kazhdan-regular-block-periodizations-of-mapping-tori-are-finite.md
  - research/fpbs-shalom-property-t-is-open.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
  - research/finitely-generated-linear-groups-are-residually-finite.md
---

**ESTABLISHED.** Proof: `kazhdan-multiplicity-rigidity-kills-exact-cover-models-proof`.
It is elementary, apart from Shalom openness of (T), the finite automorphic presentation of a
finitely presented mapping torus, and Malcev's theorem, all established in the graph.

## Setting

As in `kazhdan-regular-block-periodizations-of-mapping-tori-are-finite` (RB): `K` is finitely
generated Kazhdan, `φ ∈ Aut(K)`, `G = K ⋊_φ Z` is finitely presented, and

```text
G = < S, t | R_0 , t s t^-1 = w_s (s in S) >,   K~ = <S | R_0> Kazhdan.
```

Let `ŵ : F_S -> F_S` be `s ↦ w_s`, and put

```text
R_1 = R_0 ∪ ŵ(R_0),     K~_1 = <S | R_1>.
```

Every element of `R_1` is a relator of `K`. Let `κ` be a Kazhdan constant of `K~` for `S`,
`q = |S ∪ S^-1|`, `L = max_(r in R_0) |r|`, and

```text
m_0 = ⌈ 4 q ln 4 / κ² ⌉,     δ_0 = 1/m_0.
```

## Statement

**(MR) Multiplicity rigidity.** Let `α, β` be unitary representations of `K~` on the same
finite-dimensional space, with `‖α(s) − β(s)‖ < δ_0` for all `s` in `S` (operator norm). Then
`α` and `β` are unitarily equivalent. `δ_0` does not depend on the dimension.

**(EC) Exact-cover wraps are exact.** Let `U` be a unitary representation of `K~_1` on `C^k`,
and `T ∈ U(k)` any unitary with

```text
max_(s in S) ‖T U(s) T* − U(w_s)‖ < δ_0.
```

Then there is a unitary `T'` such that `s ↦ U(s)`, `t ↦ T'` is a representation of `G`. So
`U` factors through `K`. If `K` has no nontrivial finite quotient, then `U(s) = 1` for all `s`.

**(GP) Gapped blocks need only `R_0`.** Suppose instead that `U` is a representation of `K~`
only, and that it is `c`-gapped: `‖U(x) − 1‖ ≥ c` whenever `U(x) ≠ 1`. If the defect in (EC)
is `< min(δ_0, c/L)`, then `U` is a representation of `K~_1`, and (EC) applies. Every direct sum
of permutation representations of finite quotients of `K~` is `√3`-gapped.

**(AS) Corona form.** Let `Θ : G -> U(∏ M_(k_n) / ⊕ M_(k_n))` be any norm-corona model, and
suppose `Θ|_K` is **R_1-liftable**: there are representations `ρ_n` of `K~_1` on `C^(k_n)` with
`Θ(s) = [(ρ_n(s))_n]` for `s` in `S`. If `K` has no nontrivial finite quotient, then `Θ|_K`
is trivial. The same holds for `√3`-gapped representations of `K~`.

**(RL) Reformulation.** If `K` is Kazhdan and has no nontrivial finite quotient, and `G` is
finitely presented, then

```text
Rad_MF(G) = K × {0}   iff   every norm-corona model of G is R_1-liftable on K.
```

The forward direction is trivial, since a model trivial on `K` lifts by `ρ_n = 1`.

## Applications

- **LEF kernels.** Let `K` be LEF and quotientless. Take local embeddings `ι_n` of balls of
  radius `r_n → ∞` into finite groups `Q_n`, and any finite-dimensional unitary representations
  `π_n` of `Q_n`. Then `ρ_n = π_n ∘ ι_n` is a representation of `K~_1` once `r_n ≥ L·max_s|w_s|`.
  So by (AS), no norm-corona model of `G` restricts on `K` to `[π_n ∘ ι_n]`, or to anything
  asymptotic to it, for **any** wrap. This includes the models of `lef-implies-operator-mf`
  (`π_n` regular) that make `K` MF. It applies to every witness of (LK3) in
  `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`.
- **All Kazhdan-kernel witnesses.** By `mapping-torus-mf-radical-lies-in-finite-residual`, every
  witness of (LK3), of `mf-kazhdan-quotientless-mapping-torus-exact-radical`, and every
  Kazhdan-kernel witness of `torsion-free-sofic-exact-mf-radical-over-z` has `K` quotientless.
  So (EC), (GP) and (AS) hold for all of them.
- **RB extended.** (GP) with `c = √3` contains RB's class, with the block-monomial hypothesis on
  `T` removed and with Gassmann-type permutation blocks allowed. The HS count of RB section 4
  allows a multiplicity mismatch of relative size `(δ/κ)²`. (MR) shows that in operator norm the
  mismatch is exactly zero below `δ_0`. That answers the question left there ("whether an
  operator-norm `T` can realise such a mismatch"): it cannot, for exact-cover blocks.

## What this kills

**The class.** Every attempt to build an operator-norm model of `G` that is nontrivial on `K`
from representations that satisfy the finitely many relators `R_1 = R_0 ∪ ŵ(R_0)` exactly (or
`R_0` exactly, with a uniform norm gap). Blocks, multiplicities, images (finite or infinite) and
the wrap unitary `T` are all arbitrary. This includes:

- all periodized towers;
- every representation of LEF local groups;
- every permutation-module (sofic-to-norm) block model.

**The invariant.** The multiplicity function `σ ↦ m_σ` on irreducible representations of the
Kazhdan cover `K~`. The Kazhdan average `h'` on `ρ ⊗ σ̄` has spectrum in `[0, 1 − κ²/4q] ∪ {1}`.
So its `m_0`-th power is within `1/4` of the projection onto `Hom(σ, ρ)`. Operator-norm
closeness `δ < δ_0` moves that power by less than `1/2`. So the two projections have equal rank.

**Where every member dies.** At the wrap. `T U T*` and `U ∘ ŵ` are both genuine
representations of `K~`, so (MR) replaces `T` by an exact intertwiner `T'`. Then `(U, T')`
satisfies the finite presentation of `G` exactly. Exactness propagates along `φ` to all of the
infinitely many relators of `K`. Malcev then makes the image of `K` residually finite, so a
quotientless `K` dies.

**What survives.** A model of a witness that is nontrivial on `K`, if one exists, has `Θ|_K`
**not R_1-liftable**. Its `K`-part is an asymptotic representation of the finitely presented
Kazhdan group `K~_1` that is not asymptotic to genuine representations of `K~_1`. So it is a
witness of norm instability of `K~_1` at a point factoring through `K`. The rigidity (MR) holds
for genuine representations only; almost-representations of `K~` are not covered, and no
argument here excludes them.

**Positive reading.** By (RL), the radical equation for a quotientless Kazhdan kernel with a
finitely presented mapping torus is equivalent to a **relative stability** property of one
finitely presented Kazhdan cover: every corona representation of `K` that extends to `G` lifts
exactly on the finite set `R_1`. In particular, it would follow from operator-norm matricial
stability of `K~_1`. No infinite Kazhdan group is recorded in the graph as norm-stable, so this
reduction is recorded without a claim that it closes anything.
