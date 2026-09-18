---
rg: 2
id: fp-piecewise-projective-groups-specialize-to-algebraic-data
kind: claim
title: A finitely presented group of one-dimensional piecewise-projective maps with arbitrary real data specializes to real algebraic data nontrivially on any finite set, so it has solvable word problem, and each of its finitely generated simple subgroups embeds in such a group over a real number field and has polynomial-time word problem
distinct_from:
  fp-bieri-strebel-line-groups-are-deformation-rigid: that shows a finitely presented Bieri--Strebel line group has algebraic slopes, from its explicit presentation; this applies to every finitely presented group of piecewise-projective maps of an interval, circle or line, and concludes only that finite pieces of the group, and its simple subgroups, live over real algebraic data.
  fp-pl-groups-with-f-have-no-transcendental-support-endpoints: that kills finite presentation for PL groups containing a dyadic F and a transcendental bump endpoint; this does not decide finite presentation of any given group, but bounds the word problem of every finitely generated simple subgroup of every finitely presented piecewise-projective group.
  complexity-bounded-host-classes-are-not-universal: that says host classes with one recursive word-problem bound are not universal; this places the finitely generated simple subgroups of all finitely presented one-dimensional piecewise-projective groups in polynomial time, with no restriction on their real parameters.
---

**ESTABLISHED** (lane proof, elementary given Tarski--Seidenberg; not reviewed). No priority is
claimed. The method is the standard specialization argument, as for finitely presented residually
finite groups. It was not found stated for piecewise-linear groups with real parameters in the sources
read by the swarm; no literature search beyond them was done.

## Setting

Let `X = [0,1)`. A *PP map* is a bijection `g` of `X` with breakpoints
`0 = x_0 < x_1 < ... < x_n = 1` such that on each `[x_{i−1}, x_i)` it is an increasing real Möbius
map `x ↦ (ax+b)/(cx+d)` onto a half-open interval. Discontinuities are allowed, as in Thompson's `V`.
PL maps (`c = 0`, `d = 1`) are the main case: `F`, `T`, `V`, Stein and Bieri--Strebel groups, and
irrational-slope groups. Lodha--Moore and Monod groups are piecewise projective. The *data* of `g` are its breakpoints and matrix
entries. For a subfield `K ⊆ R`, `PP_K` is the group of PP maps with all data in `K`.

The circle `R/Z` (cut at `0`) and the line `R` (a projective chart of `RP^1`, with unbounded end
pieces) are handled by the same proof, with the same conclusions.

## Statement

Let `G = ⟨g_1,…,g_m | r_1,…,r_q⟩` be finitely presented, with a faithful homomorphism
`φ_0 : G → PP_R`.
1. **Specialization.** For every finite `F ⊂ G ∖ {1}` there is a homomorphism `φ : G → PP_K`,
   with `K` a real number field, such that `φ(f) ≠ 1` for all `f ∈ F`.
2. **Word problem.** `G` has solvable word problem.
3. **Simple subgroups.** Every finitely generated simple subgroup `H ≤ G` embeds in a finitely
   generated subgroup of `PP_K` for some real number field `K`. Hence `H` has word problem solvable
   in polynomial time. In particular, every finitely presented simple group of PP maps (of an
   interval, the circle or the line) is isomorphic to one with real algebraic data and has
   polynomial-time word problem.

## Proof

**Parameter space.** Fix the number of pieces of each `φ_0(g_i)` and the order of their images. The
data of all generators form a point `θ_0 ∈ R^D`. For `θ ∈ R^D` let `φ_θ(g_i)` be the maps with these
data. Let `Θ` be the set of `θ` for which each `φ_θ(g_i)` is a PP map of the fixed type and
`φ_θ(r_k)` is the identity for all `k`.
- "`φ_θ(g_i)(x) = y`" is a first-order formula over the ordered field `R`, with rational constants,
  in `θ, x, y`.
- So is "`∀x, φ_θ(r_k)(x) = x`".
- By Tarski--Seidenberg, `Θ` is semialgebraic and defined over `Q`, and `θ_0 ∈ Θ`.
- Every `θ ∈ Θ` defines a homomorphism `φ_θ : G → PP_R`, since the relators hold.

**Algebraic points are dense in `Θ`.** Let `R_alg` be the real algebraic numbers, a real closed
field and an elementary substructure of `R`. For a rational point `θ'` and rational `ε > 0`, the
sentence "`∃θ ∈ Θ` with `|θ − θ'| < ε`" has rational parameters. If it holds in `R`, it holds in
`R_alg`. So every neighbourhood of `θ_0` contains points of `Θ ∩ R_alg^D`. Such a point has
coordinates in a real number field `K`, and `φ_θ(G) ≤ PP_K`.

**Nontriviality is open.** Let `f ∈ F`, written as a word `f = s_1 ⋯ s_L` in the generators.
- The map `φ_0(f) ≠ 1`, and on each piece a Möbius map has at most two fixed points unless it is the
  identity there. So `φ_0(f)` moves every point of some open interval.
- Choose there a point `p` whose partial images `s_{i+1} ⋯ s_L (p)` (under `φ_0`) avoid the finitely
  many breakpoints of the next letter.
- For `θ` near `θ_0` the orbit of `p` stays in the interiors of the same pieces. So `φ_θ(f)(p)` is a
  continuous function of `θ`, and it stays `≠ p`.

**Item 1.** Take `θ ∈ Θ ∩ R_alg^D` close enough to `θ_0` for all `f ∈ F`.

**Item 2.** Trivial words are recursively enumerable, since `G` is finitely presented. Nontrivial
words are recursively enumerable too. Enumerate the algebraic points `θ` (by minimal polynomials and
isolating intervals). For each, decide `θ ∈ Θ` and `φ_θ(w) ≠ 1` by exact real algebraic arithmetic,
or by Tarski's decision procedure. If `w ≠ 1` in `G`, item 1 with `F = {w}` gives such a `θ`. If
`w = 1` in `G`, then `φ_θ(w) = 1` for every `θ ∈ Θ`.

**Item 3.** Pick `h ∈ H ∖ {1}` and apply item 1 to `F = {h}`. The restriction `φ|_H` has a proper
kernel, which is normal in `H`, so it is trivial. Thus `H ≅ φ(H) ≤ PP_K`, and `φ(H)` is
finitely generated.

**Polynomial time over a number field.** Let `Γ ≤ PP_K` be finitely generated, with `K = Q(β)`,
`β` a real algebraic integer. Scale each generator's matrices to have entries in `Z[β]`, and write
points projectively as `(p : q)` with `p, q ∈ Z[β]`.
- **Sizes.** For a word of length `l`, the composed map has at most `N·l` pieces, where `N` bounds
  the pieces of the generators. Each breakpoint is a preimage of a generator breakpoint under at
  most `l` fixed Möbius maps. Each piece's matrix is a product of at most `l` fixed matrices. In
  homogeneous coordinates every step is linear with fixed coefficients, so all entries have
  bit-size `O(l)`.
- **Comparisons.** Comparing `(p:q)` with `(p':q')` is the sign of `pq' − p'q` times the signs of
  `q` and `q'`: signs of elements of `Z[β]` of bit-size `O(l)`. A nonzero algebraic integer has norm
  of absolute value at least `1`, and its other conjugates have size `2^{O(l)}`. So it has absolute
  value at least `2^{−O(l)}`, and computing `β` to `O(l)` bits decides the sign.
- **Identity.** The word is trivial iff every piece's matrix is scalar.

This takes `O(l^2)` comparisons, each in time polynomial in `l`. The word problem of `H` reduces to
that of `φ(H)` by a length-linear substitution. ∎

## Consequences

- **Hard parameters die in every one-dimensional piecewise-projective host.**
  `hard-slope-thompson-groups-have-no-piecewise-projective-hosts`: for the Liouville slopes of
  `transcendental-slope-thompson-groups-have-hard-word-problems`, the simple group `D(V_λ)` embeds
  in no finitely presented group of PP maps. This settles the "still open" piecewise-projective
  part of Attempt 8 on `fp-simple-groups-with-arbitrarily-complex-word-problem`. Every finitely
  generated simple group in such a host has polynomial-time word problem, whatever the real
  parameters.
- **Contrast with finite generation.** Finitely generated PP groups can have unsolvable word
  problem, for example `D(V_λ)` with noncomputable `λ`
  (`stein-derived-groups-need-computable-modules`). Item 2 shows that finitely presented ones never do.
- **Dimension one matters.** In `nV`, piecewise affine on `[0,1)^n`, the pieces of a product can
  multiply, and the word problem is coNP-complete (Birget). The polynomial bound above uses the
  linear growth of breakpoints on a line.

## Lesson for general BH

- **The mechanism.** Finite presentation plus a tame (semialgebraic, bounded-dimension) action gives
  specialization to algebraic data, the real-closed-field analogue of Mal'cev's argument for
  residually finite groups. Continuous parameters in a host therefore never raise the complexity of
  its simple subgroups.
- **Host complexity.** The complexity comes only from combinatorial growth of pieces: linear on a
  line, exponential for boxes (`fp-simple-real-box-map-groups-are-not-universal-hosts`).
- **Consequence.** Every finite-dimensional real-geometric host class is capped. A universal BH
  construction must be symbolic and infinite-dimensional, with the input's algorithm simulated in
  its dynamics.
