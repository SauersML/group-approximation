---
rg: 2
id: brick-groupoid-not-isomorphic-to-kazhdan-host
kind: claim
title: "The brick groupoid G_2^n is not isomorphic to the amenable Kazhdan host (M x| Gamma) x G_2, equivalently their diagonals are non-conjugate Cartan subalgebras of O_2"
distinct_from:
  nv-brick-groupoid-and-kazhdan-host-are-both-o2: that computes the two reduced C*-algebras and finds them both O_2, so no algebra-level invariant decides this; this is the remaining groupoid-level (Cartan-pair) question itself.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that constructs the host and lists the properties it shares with G_2^n; this asks whether the two groupoids are actually distinct.
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is about all Kazhdan subgroups of nV; this is the single test case Gamma = Z^3 x| SL_3(Z) inside one explicitly built groupoid, and it is implied by that claim.
artifacts: []
---

**Status: OPEN.**

## Statement

Let `G_2^n` be the brick groupoid of `nV` and let `𝒢_W1 = (M ⋊ Γ) × G_2` be the host of
`amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`, with
`Γ = Z^3 ⋊ SL_3(Z)`. Then `G_2^n ≇ 𝒢_W1` as topological groupoids, for every `n ≥ 1`.

Equivalent forms (both groupoids are second countable, Hausdorff, ample, minimal and
effective, so `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids` applies,
and both algebras are `O_2` by `nv-brick-groupoid-and-kazhdan-host-are-both-o2`):

- there is no isomorphism `C*_r(G_2^n) → C*_r(𝒢_W1)` carrying `C(C^n)` onto `C(M × C)`;
- the two canonical diagonals are **non-conjugate Cartan subalgebras of `O_2`**.

The same statement for `𝒢_RS = (Γ' ⋉ Ω) × G_2` (`rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`)
is part of this node.

## Role: a necessary prerequisite of the flagship, which can fail on its own

`[[·]]` is a groupoid invariant, so `G_2^n ≅ 𝒢_W1` would give `nV ≅ [[𝒢_W1]] ⊇ Γ`, an
infinite Kazhdan subgroup. Hence this claim is **necessary** for
`brin-thompson-groups-nv-are-a-t-menable` and for
`kazhdan-subgroups-of-brin-thompson-groups-are-finite`, via the route
`brick-host-nonisomorphism-from-nv-haagerup`. If it fails, Zaremsky Problem 2.7 is
answered negatively, and by an explicit isomorphism rather than by any cnd-function
argument.

It can fail on its own in the sense that deciding it is a rigidity question about one
pair of Cartan subalgebras of one algebra, with no reference to conditionally negative
definite functions, walls, cocycles or distortion.

## Attempts

- **Separate them by a C\*-invariant (dies).** `nv-brick-groupoid-and-kazhdan-host-are-both-o2`:
  the two reduced C\*-algebras are isomorphic, both being `O_2`. Every invariant of the algebra
  — K-theory, traces, ideals, Cuntz semigroup, nuclear dimension, `Z`-stability, UCT — takes the
  same value. Dies at the isomorphism itself.
- **Separate them by groupoid homology (dies).** `H_*(𝒢 × G_2) = 0` for every étale `𝒢`
  (`matui-groupoid-homology-kunneth-and-full-shift-vanishing`), and both groupoids are of that
  form. Dies at the Künneth formula, because `H_*(G_2) = 0` annihilates whatever the other
  factor carries. Matui's index map `[[𝒢]] → H_0(𝒢)` is therefore zero on both — but note
  (referee lens 3, 2026-09-18) that this does **not** give `[[𝒢]]^ab = 0`: vanishing `H_0`
  and `H_1` force trivial abelianization only under the unproved AH conjecture. So the
  abelianization of the full group is not known to separate them, and is not known to fail
  to.
- **Separate them by a dynamical property (dies).** Minimality, effectiveness, pure
  infiniteness, amenability, absence of an invariant probability measure and compact generation
  hold for both (`amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`); expansivity
  holds for `𝒢_RS` too (`rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`).
- **Separate them by the AF-by-`Z^n` cocycle (open; the surviving attack).** `G_2^n` has one
  (`brick-groupoid-has-zn-cocycle-with-af-kernel`). The obvious cocycle on the host, `(h, g) ↦
  c_{G_2}(g)`, has kernel `(M ⋊ Γ) × R_2 ⊇ M ⋊ Γ`, whose full group contains `Γ` and is
  therefore not locally finite, so that kernel is not AF. Lemma B of
  `af-by-zk-full-groups-have-finite-kazhdan-subgroups` upgrades this to *every* cocycle that
  vanishes along `Γ`. What is not settled: whether some cocycle almost faithful along `Γ`
  exists. That is where this node now sits.
- **Deferred.** Matui's isomorphism classification of products of SFT groupoids
  (arXiv:1512.01724) is not applicable until the host is known to be, or not to be, such a
  product — which is this question.
- **2026-09-19 (swarm-0917-w16-w16-nv-break, finite-models): the isotropy stratification
  separates, and the W1 half is settled.**
  - *Invariant.* The cardinality of the top isotropy stratum.
    - In `G_2^n` the isotropy at `x` is `Z^{p(x)}`, where `p(x)` counts the eventually periodic
      coordinates.
    - So the rank-`n` set is `E^n`, which is countable.
    - Isomorphisms carry isotropy groups to isotropy groups. No topology is used.
  - *Theorem (ESTABLISHED, self-contained).* `brick-groupoid-has-no-principal-cantor-factor`.
    - `G_2^n ≇ 𝒫 × 𝒦` whenever `𝒫` is principal with uncountable unit space.
    - More generally, an isomorphism forces countable top strata in both factors.
    - This gives `G_2^n ≇ 𝒢_W1 = (M ⋊ Γ) × G_2` for every `n ≥ 1`, since `Γ ↷ M` is free.
    - It also rules out isomorphisms between nonempty open reductions, so it covers Kakutani
      equivalence too.
  - *Death step for the whole class.* Every "free Cantor model × amplifier" host dies at the
    count: `(top of 𝒫) × (top of 𝒦)` is uncountable, while `E^n` is countable.
  - *Correction.* "No invariant recorded on the graph separates the two groupoids" is no
    longer true, and the gate list on the flagship should add isotropy strata as a separator.
  - *Decomposition.* New route `brick-host-nonisomorphism-via-isotropy-strata`, which does not
    use the flagship.
    - It requires the established theorem.
    - It also requires the one OPEN hole `brick-groupoid-not-isomorphic-to-rs-boundary-host`.
      That hole is already reduced: an isomorphism would force every `Γ_ω` to be free abelian,
      the action to be non-free, and the maximal stabilizer rank `n − 1 ≥ 1` to be attained
      on a countable set.
    - A conditional sketch there, through the non-regular isotropy locus, would finish the RS
      half given a regular split `Z^2 ≤ Γ`.
  - *Status.* This node stays OPEN only through its RS half.

## What is known

- No invariant recorded on the graph separates the two groupoids. Killed as separators:
  minimality, effectiveness, pure infiniteness, amenability, absence of an invariant
  measure, compact generation (`amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`),
  expansivity (`rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`), the whole
  isomorphism class of `C*_r` including K-theory, traces, ideals, Cuntz semigroup and
  nuclear dimension, and Matui's groupoid homology
  (`nv-brick-groupoid-and-kazhdan-host-are-both-o2`).
- The first candidate separator is the AF-by-`Z^n` structure: `G_2^n` has a continuous
  `Z^n`-cocycle with AF kernel (`brick-groupoid-has-zn-cocycle-with-af-kernel`), and it is
  open whether `𝒢_W1` has one. Lemma B of
  `af-by-zk-full-groups-have-finite-kazhdan-subgroups` is the first constraint: such a
  cocycle on `𝒢_W1` must be almost faithful along `Γ`.
- Matui, *Étale groupoids arising from products of shifts of finite type*,
  arXiv:1512.01724, "completely determine[s] when these product groupoids are mutually
  isomorphic" — but only inside the class of products of SFT groupoids, which `𝒢_W1` is
  not known to be outside of, because that is this question.
