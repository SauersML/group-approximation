---
rg: 2
id: finite-state-li-coded-full-groups-have-exponential-word-problem
kind: claim
title: Finitely generated subgroups of full groups of effective Li-coded groupoids with N^k degrees and finite-state unit data have word problem in time 2^(C l^2), so no such host class is universal
distinct_from:
  finite-k-graph-full-groups-have-exponential-word-problem: that is the case with trivial unit groups (finite k-graphs); this allows infinite unit groupoids acting self-similarly with finite-state data, which covers Katsura–Exel–Pardo hosts, Röver–Nekrashevych groups of automaton groups and the finite-unit building categories.
  rational-homeomorphism-subgroups-have-exponential-wp: that bounds rational homeomorphism groups (one-object, one-colour codings); this is the multi-object, rank-k version with unit groupoids.
  finitely-coded-cantor-actions-give-type-a-hosts: that shows these hosts are type (A) once finitely presented; this caps what they can contain.
  complexity-bounded-host-classes-are-not-universal: that is the general non-universality principle; this supplies the uniform exponential bound for the whole class.
---

**ESTABLISHED** (lane proof, bh-g3-libridge 2026-09-18, inline below; not independently
reviewed; no priority claimed). The one standard input, that a finite-state self-similar action
decides trivial action by a closure over section-words, is proved inline.

## Setting (the class `𝒦_fs`)

`ℭ` is a left cancellative small category with finitely many objects and a degree functor
`d : ℭ -> N^k` with `d^{-1}(0) = ℭ^*`, satisfying (UFP*) (arXiv:2110.04505v2, l.1837), with no
sources (every object receives a morphism of every degree `e_i`), and locally finite: finitely many
morphisms of each degree into each object, modulo right units. **Finite-state data** means there
are a finite set `S ⊆ ℭ^*` generating the unit groupoid, closed under inverses and containing the
identities, and for each colour `i` and object `v` a finite set `R_i(v)` of representatives of the
degree-`e_i` morphisms into `v` modulo right units, such that:

- **(fs1)** for `s ∈ S` and `r ∈ R_i(d(s))`, `s r = r' s'` with `r' ∈ R_i(t(s))` and `s' ∈ S`;
- **(fs2)** for `r ∈ R_i(v)` and `r̃ ∈ R_j(d(r))` with `i ≠ j`, `r r̃ = r̃' r' s'` with
  `r̃' ∈ R_j(v)`, `r' ∈ R_i(d(r̃'))` and `s' ∈ S`.

`𝒢 = I_l ⋉ ∂Ω` is assumed effective, so `F(𝒢)` is a group of homeomorphisms of a union `Z` of
object boundaries. Condition (F) is not needed. Examples: finite `k`-graphs (`S` = identities),
Katsura–Exel–Pardo groupoids with finite-state actions (e.g. the odometer host of `2V_τ`),
Röver–Nekrashevych groups of automaton groups (one object, one colour), and the finite-unit
categories of the Ã₂, tree-product and Euclidean-building hosts.

## Statement

1. **Word problem.** Every finitely generated `H ≤ F(𝒢)` has, for any finite generating set, a
   word-problem algorithm running in time `C_H · 2^{C_H l^2}` on words of length `l`. If every unit
   in (fs2) is an identity (Zappa–Szép products of `k`-graphs with finite-state self-similar
   groupoids, as in Katsura–Exel–Pardo and Li's Example ZS), the bound improves to `C_H · 2^{C_H l}`.
2. **Non-universality.** By `complexity-bounded-host-classes-are-not-universal` with `T(l) = 2^{l^2}`,
   some two-generated group with solvable word problem embeds in no `F(𝒢)`, `𝒢 ∈ 𝒦_fs`.

## Proof

1. **Normal forms of morphisms.** Using (fs2) repeatedly, every morphism is `r_1 ⋯ r_N · w` with
   `r_j` representatives in a fixed colour order and `w` a unit; (UFP*) makes the representative part
   unique, so `c =^* c'` (i.e. `cX = c'X`) is decided by comparing representative parts. Each (fs2)
   move adds one generator of `S`, and pushing a unit word through a representative by (fs1) keeps
   its length. So a morphism of degree `≤ D`, written as a product of `≤ kD` generating morphisms,
   has a normal form with trailing unit word of length `≤ (kD)^2`.
2. **Pieces.** No sources and (UFP*) make the degree-`p` cylinders at `v` a partition of `X(v)` for
   each `p`. So each generator of `H` is, by compactness, a finite table of pieces `(δ, u, γ)` with
   `δ z ↦ γ u z` on `δX(d(δ))`, and inverses swap `δ, γ` and invert `u`. Fix `D` bounding the
   degrees of all `δ, γ` in the tables of the generators.
3. **Composition.** Compose a piece `(δ', u', γ')` with a generator table: refine `γ'X` by the
   degree-`D` cylinders `γ' f X`; pull back through `u'` (by (fs1), `u'^{-1} . f` is a
   representative path and the section is a word of the same length). Then factor `γ' f` by
   (UFP*) as `δ f'' w''` with `δ` the unique matching domain piece, and push the target unit through
   `f''`. The result is a piece `(δ' f_1, u_new, γ (u . f''))` whose degrees grow by `≤ D`.
   Its unit word is `(u|_{f''}) · w'' · (u'|_{f_1})`. Sections keep length by (fs1). `w''` comes from
   the (fs2) moves that extract a degree-`≤ D` prefix from the colour-ordered form of `γ' f`: there
   are at most `k^2 D (Dt + D)` of them at step `t`, and none in the Zappa–Szép case. So after `l`
   steps unit words have length `≤ K l^2`, or `≤ K l` in the Zappa–Szép case, with `K` depending only
   on the generating data. Each composition multiplies the number of pieces by at most `M`, the
   largest number of degree-`D` cylinders at an object. A word of length `l` thus gives `≤ M^l`
   pieces with degrees `≤ Dl`, computed in time `M^l · poly(l)`.
4. **Identity test.** `F(𝒢)` acts faithfully on `Z` by (Eff), so the product is trivial iff every
   piece `(δ, u, γ)` is the identity map on `δX(d(δ))`. This holds iff `γ = δ w` for a unit `w`
   (decided by step 1) and the unit word `w u` acts trivially on `X(d(δ))` (step 5).
5. **Trivial action of a unit word.** A unit word `x` of length `m` acts trivially on `X(v)` iff it
   fixes every cylinder. By (fs1) the sections of `x` at representative paths are again words of
   length `≤ m` over `S`. So `x` acts trivially iff every word `x'` in the closure `Σ(x)` of `{x}`
   under taking sections at single representatives satisfies `x' . r = r` for every representative
   `r` (induction on path length). `Σ(x)` has `≤ |S|^{m+1}` elements and is computed in time
   `|S|^{O(m)}`.
6. **Total.** `M^l` pieces, each tested in time `|S|^{O(K l^2)}` (or `|S|^{O(Kl)}` in the
   Zappa–Szép case), gives time `C · 2^{C l^2}` (or `C · 2^{C l}`). Item 2 is then
   `complexity-bounded-host-classes-are-not-universal`. ∎

## Remark (not claimed): Li's general degree setting

The proof uses only that normal forms are computed from finite tables. The same count should go
through for Li's degree maps to a left cancellative monoid `P` with a finite Garside family and
conditional lcms (arXiv:2110.04505v2, `thm:deg`), where the greedy normal form is computed from the
finite lcm table of the simples. So Li's finiteness theorems, applied with finite-state unit data,
certify only exponential-time hosts. Beyond finite-state data, Li's own word-problem corollary
(`intro:WordProblem`, via a computable `=^*`-map) shows that the full group's word problem reduces
to the unit sections with exponential overhead.

## Lesson for general BH

Every host whose finiteness comes from a Garside or unique-factorization calculus (Li's
theorems, k-graph full groups, Röver–Nekrashevych groups of automaton groups) computes normal forms,
and normal forms computed from finite tables cap the word problem at a fixed elementary bound (`2^{C l^2}`). So the
hosts that universal Boone–Higman needs cannot come from Li's theorem with finite-state data. The
hardness must enter either through non-finite-state self-similar units, which are residually finite
(`finitely-coded-groupoid-unit-groups-are-residually-finite`), or through a finiteness
theorem that produces no normal form. That is the "non-deterministic finite type ⇒ finite
presentation" theorem the master route calls FTR.
