---
rg: 2
id: thompson-f-co-amenable-host-gate-proof
kind: route
title: Instantiate the relative Schreier gate at H = F using Brin-Squier, torsion-freeness, Farley's a-T-menability and the normal subgroup structure of F
target: thompson-f-co-amenable-hosts-have-no-free-or-kazhdan-subgroups
requires:
  - co-amenable-hosts-inherit-the-relative-schreier-gate
  - thompson-f-has-no-free-subgroups
  - thompson-f-has-infinite-cohomological-dimension
---

Let `G` be a host: `F ≤ G` and `F` is co-amenable in `G`. Write `L_g = Λ ∩ gFg^{-1}` for a subgroup
`Λ ≤ G`.

**Why a host must be non-amenable to be useful.** If `G` is amenable then so is its subgroup `F`.
If `G` is non-amenable then `F` is non-amenable, because an invariant mean on `F` composed with the
invariant mean on `G/F` is an invariant mean on `G`. So `F` is amenable iff `G` is, and the route
`thompson-f-is-not-amenable` by hosts needs an *independent* proof that `G` is non-amenable. ∎

---

## Item 1: no non-abelian free subgroup

`thompson-f-has-no-free-subgroups` (Brin and Squier, Invent. Math. 79 (1985) 485-498) is
ESTABLISHED: `F` contains no non-abelian free subgroup. Apply item 2 of
`co-amenable-hosts-inherit-the-relative-schreier-gate` with `H = F`: a group co-amenably containing
a group with no non-abelian free subgroup has no non-abelian free subgroup. ∎

### `V` is not a host: an explicit free subgroup

Recall `V` is the group of homeomorphisms of `2^N` given by finite prefix-replacement tables: for
any two partitions of `2^N` into the same finite number of cylinders, the bijection matching them
in order by prefix replacement lies in `V`. Write `[u]` for the cylinder of finite words with
prefix `u`.

Define `a ∈ V` by the table on the partition `{[00], [10], [11], [0100], [0101], [011]}`:

  `[00] ↦ [0000]`, `[10] ↦ [0001]`, `[11] ↦ [001]`, `[0100] ↦ [01]`, `[0101] ↦ [10]`, `[011] ↦ [11]`.

The images partition `2^N` as `{[0000], [0001], [001], [01], [10], [11]}`, so `a ∈ V`, and

  `a(2^N ∖ [01]) = [0000] ∪ [0001] ∪ [001] = [00]`,  `a([01]) = [01] ∪ [10] ∪ [11] = 2^N ∖ [00]`.

Define `b ∈ V` by the table on `{[00], [01], [10], [111], [11000], [11001], [11010], [11011]}`:

  `[00] ↦ [1000]`, `[01] ↦ [1001]`, `[10] ↦ [1010]`, `[111] ↦ [1011]`,
  `[11000] ↦ [00]`, `[11001] ↦ [01]`, `[11010] ↦ [110]`, `[11011] ↦ [111]`.

Both lists are partitions of `2^N` (the first because `[110] = [11000] ∪ [11001] ∪ [11010] ∪
[11011]`, the second because `[10] = [1000] ∪ [1001] ∪ [1010] ∪ [1011]`), so `b ∈ V`, and

  `b(2^N ∖ [110]) = [10]`,  `b([110]) = [00] ∪ [01] ∪ [110] ∪ [111] = 2^N ∖ [10]`.

Put `A^+ = [00]`, `A^- = [01]`, `B^+ = [10]`, `B^- = [110]`; these are pairwise disjoint and
nonempty, and `[111]` is disjoint from all four. The four displayed identities say

  `a(X ∖ A^-) ⊆ A^+`, `a^{-1}(X ∖ A^+) ⊆ A^-`, `b(X ∖ B^-) ⊆ B^+`, `b^{-1}(X ∖ B^+) ⊆ B^-`.

**Ping-pong.** Let `w = g_k ⋯ g_1` be a nonempty reduced word in `a^{±1}, b^{±1}`, and let
`S(a) = A^+`, `S(a^{-1}) = A^-`, `S(b) = B^+`, `S(b^{-1}) = B^-`. Fix `x ∈ [111]`. By induction
`g_i ⋯ g_1(x) ∈ S(g_i)`: for `i = 1`, `x` lies outside all four sets, so each of the four
identities applies; for the step, `g_i ⋯ g_1(x) ∈ S(g_i)` and `g_{i+1} ≠ g_i^{-1}` by reducedness,
so `S(g_i) ≠ S(g_{i+1}^{-1})` and `g_i ⋯ g_1(x)` lies in the complement of the set removed by the
identity for `g_{i+1}`. Hence `w(x) ∈ S(g_k)`, which is disjoint from `[111]`, so `w(x) ≠ x` and
`w ≠ 1`. So `⟨a, b⟩ ≤ V` is free of rank `2`, and `V` is not a host. ∎

`T` contains a copy of `PSL_2(Z) ≅ Z/2 * Z/3`, hence a non-abelian free subgroup, by Thurston's
identification of `T` with the group of piecewise-`PSL_2(Z)` homeomorphisms of the circle (Cannon,
Floyd and Parry, *Introductory notes on Richard Thompson's groups*, Enseign. Math. 42 (1996), §7;
Ghys and Sergiescu, Comment. Math. Helv. 62 (1987) 185-239). Cited, not re-read. `V ≤ nV` for
`n ≥ 1`, so no `nV` is a host either.

### Tits-alternative classes

Every class in the table of the claim has the property that its non-amenable members contain a
non-abelian free subgroup, so item 1 excludes all of them at once. The citations, all standard and
not re-read here: Tits (finitely generated linear groups), Gromov and Bowditch (non-elementary
hyperbolic and relatively hyperbolic groups), Osin, *Acylindrically hyperbolic groups*, Trans. AMS
368 (2016) (every acylindrically hyperbolic group contains a non-abelian free subgroup), Ivanov and
McCarthy (mapping class groups), Bestvina, Feighn and Handel (`Out(F_n)`), Sageev and Wise
(groups acting properly cocompactly on `CAT(0)` cube complexes), Margulis, *Free subgroups of the
homeomorphism group of the circle*, C. R. Acad. Sci. Paris 331 (2000) 669-674 (a subgroup of
`Homeo_+(S^1)` either preserves a probability measure or contains a non-abelian free subgroup).

---

## Item 2: no non-amenable torsion subgroup

`thompson-f-has-infinite-cohomological-dimension` is ESTABLISHED and records that `F` is
torsion-free. Apply item 3 of `co-amenable-hosts-inherit-the-relative-schreier-gate`: for a torsion
subgroup `Λ ≤ G`, each `L_g = Λ ∩ gFg^{-1}` is a torsion subgroup of a group isomorphic to `F`,
hence trivial, so `Λ` is amenable. ∎

The free Burnside groups `B(m,n)` for large odd `n` (Adian), Ol'shanskii's Tarski monsters and
Nekrashevych's simple torsion groups are torsion, so none of them can appear inside a host as a
non-amenability certificate; being torsion they also contain no copy of the torsion-free `F`, so
none of them is a host.

---

## Item 3: no infinite Kazhdan subgroup

**Imported, by citation.** D. Farley, *Proper isometric actions of Thompson's groups on Hilbert
space*, Int. Math. Res. Not. 2003, no. 45, 2409-2414: Thompson's groups `F`, `T` and `V` admit
proper actions by affine isometries on Hilbert space, i.e. they have the Haagerup property. This
graph already records the same source for `V` in `thompson-v-has-haagerup-property-citation`, whose
text states that Farley's paper "also covers `F` and `T`". Standard consequences (Cherix, Cowling,
Jolissaint, Julg and Valette, *Groups with the Haagerup property*, Progress in Mathematics 197,
Birkhauser 2001): the Haagerup property passes to subgroups, and a countable group with both
property (T) and the Haagerup property is finite. Hence no infinite subgroup of `F` has property
(T).

Now apply item 4 of `co-amenable-hosts-inherit-the-relative-schreier-gate`: if `Λ ≤ G` is infinite
with property (T) then some `L_g` has finite index in `Λ`, so `L_g` is infinite, has property (T)
and embeds in `F` — impossible. So every Kazhdan subgroup of `G` is finite. ∎

---

## Item 4: quotient closure

Let `π : G ↠ Q` with `Q` non-amenable. By item 6 of
`co-amenable-hosts-inherit-the-relative-schreier-gate`, `π(F)` is co-amenable in `Q`. Now
`π(F) ≅ F/(F ∩ ker π)`, and every nontrivial normal subgroup of `F` contains the commutator
subgroup `F'`, with `F/F' ≅ Z^2` (Cannon, Floyd and Parry, §4, Theorem 4.3 and Theorem 4.5; cited,
not re-read). If `F ∩ ker π ≠ 1` then `π(F)` is a quotient of `Z^2`, hence abelian and amenable;
an amenable co-amenable subgroup forces `Q` amenable, contradiction. So `F ∩ ker π = 1`, `π|_F` is
injective, and `Q` contains a copy of `F` co-amenably: `Q` is a host. ∎

---

## Item 5: the residual gate

This is item 5 of `co-amenable-hosts-inherit-the-relative-schreier-gate` at `H = F`, together with
the observation that a non-amenable `L_g ≤ gFg^{-1} ≅ F` makes `F` non-amenable outright. ∎

---

## Calibration: why the two dynamical mechanisms could not have done this

The established node `thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts` kills a host by
producing a `G`-space on which `F` carries an amenable witness. That method cannot reach item 1.
Take `Λ` free of rank `2` and let it act on `[0,1]` by extending, affinely across the gaps, a
planar embedding of its Gromov boundary `∂Λ ⊆ [0,1]` as a Cantor set. The action fixes `0` and `1`,
so `δ_0` is an invariant probability measure and the topological mechanism sees nothing; and the
boundary action of a free group is topologically amenable, so by Connes-Feldman-Weiss the orbit
relation is hyperfinite for *every* quasi-invariant measure, and the measured mechanism sees
nothing either. A free group is therefore invisible to both dynamical witnesses, while item 1 kills
it immediately. The two methods are genuinely complementary: item 1 does not reach the Lodha-Moore
group or `H(A)`, which have no free subgroups, and the dynamical mechanisms do not reach `V`.
