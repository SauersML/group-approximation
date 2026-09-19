---
rg: 2
id: af-by-zk-full-groups-have-finite-kazhdan-subgroups
kind: claim
title: "If a minimal effective ample groupoid carries a continuous Z^k-valued cocycle with AF kernel, then every Kazhdan subgroup of its topological full group is finite"
distinct_from:
  input-encoded-sft-groupoid-hosts-are-not-universal: that establishes the case k = 1 for one-sided shifts of finite type, through Matui's zipper proof of the Haagerup property; this is the statement for all k, for which no zipper exists (2V embeds in no zipper group) and which is exactly the hypothesis the recorded Kazhdan hosts are not known to satisfy.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that refutes the same conclusion from the hypothesis list "ample, amenable, minimal, effective, purely infinite"; this adds the AF-kernel cocycle, the one property of G_2^n that the host is not known to have.
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is the special case G = G_2^n, which this implies through brick-groupoid-has-zn-cocycle-with-af-kernel; this is the general hypothesis list, which can fail on its own through any other AF-by-Z^k host.
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's positive theorem for k = 1, the strongest known instance; this asks only for the (weaker) finiteness of Kazhdan subgroups, but for all k.
artifacts: []
---

**Status: OPEN.**

## Statement

Let `𝒢` be a second countable, Hausdorff, ample groupoid with Cantor unit space, minimal
and effective. Call `𝒢` **AF-by-`Z^k`** if there is a continuous cocycle `c : 𝒢 → Z^k`
whose kernel `ker c = c^{-1}(0)` is an AF groupoid, i.e. an increasing union of
elementary (compact open, principal, finite-orbit) open subgroupoids containing the unit
space.

**Claim (S_k).** If `𝒢` is AF-by-`Z^k`, then every subgroup of `[[𝒢]]` with property (T)
is finite.

## Why this is the gate

By `brick-groupoid-has-zn-cocycle-with-af-kernel`, the brick groupoid `G_2^n` of `nV` is
AF-by-`Z^n`; so (S_n) implies `kazhdan-subgroups-of-brin-thompson-groups-are-finite`
through the route `nv-finite-kazhdan-subgroups-via-af-by-zn`, and hence it implies the
negative half of Zaremsky Problem 2.7 (no infinite Kazhdan subgroup of `nV`).

It is the **first hypothesis list on the target that the recorded calibration worlds do
not refute**. The kills accumulated on `brin-thompson-groups-nv-are-a-t-menable` are:

| hypothesis list | world that also satisfies it |
|---|---|
| ample, amenable, minimal, effective, purely infinite | `(M ⋊ Γ) × G_2` |
| the same plus compact generation | the same |
| the same plus expansivity, no invariant measure, simple nuclear purely infinite C\*-algebra | `(Γ' ⋉ Ω) × G_2` (Robertson–Steger) |
| anything about `C*_r(𝒢)`: K-theory, traces, ideals, Cuntz semigroup, nuclear dimension, `≅ O_2` | both, by `nv-brick-groupoid-and-kazhdan-host-are-both-o2` |
| anything about `H_*(𝒢)` | both, all groups vanish |
| **AF-by-`Z^k`** | **none known** |

`(M ⋊ Γ) × G_2` and `(Γ' ⋉ Ω) × G_2` are *not known* to be AF-by-`Z^k` and are not known
not to be; see Attempts for the first constraints. Because their value on the hosts is
unknown, the AF-by-`Z^k` row is a **candidate** separator, not an established one: it is
the only row on which the hosts have not already been shown to match `G_2^n`.

**Calibration, corrected 2026-09-18 (referee lens 3).** It is *not* the case that the
`k = 1` instance of (S_k) is established.
`input-encoded-sft-groupoid-hosts-are-not-universal` item 2 is stated for **irreducible
one-sided SFT groupoids**, which are a proper subclass of the AF-by-`Z` groupoids defined
above, so it establishes (S_1) only there. The hypothesis list of (S_k) is *only* second
countable, Hausdorff, ample, Cantor unit space, minimal, effective, plus a continuous
`Z^k`-cocycle with AF kernel — no expansivity, no pure infiniteness, no shift or product
structure — and that list is satisfied by **every free minimal Cantor `Z^k`-system**: for
`𝒢 = X ⋊ Z^k` with `c(x,n) = n`, `ker c = {(x,0,x)}` is the unit space groupoid, which is
compact open, principal with singleton orbits, hence elementary, hence AF; freeness gives
principal, hence effective. So (S_1) restricted to Cantor minimal `Z`-systems is a
different theorem (amenability of those full groups, Juschenko–Monod), not cited here, and
for `k ≥ 2` the class already contains minimal Cantor `Z^2`-systems whose topological full
groups are non-amenable and contain free subgroups (Elek–Monod, Proc. AMS 2013). (S_k) is
therefore a substantially stronger and riskier statement than "the one property of
`G_2^n` the hosts lack", and a proof must survive these degenerate members.

## The tension a proof must resolve

The only known proof of the `k = 1` case is Matui's zipper action
(`sft-topological-full-groups-have-the-haagerup-property`), and that method is dead for
`k ≥ 2`: `brin-thompson-2v-embeds-in-no-zipper-group` says no group with a zipper action
has a distorted element, while `2V` has the Callard–Salo element with
`|f^N| = O(log^4 N)`. So (S_k) for `k ≥ 2`, if true, is true for a reason that does not
pass through a zipper, a wall space, a CAT(0) cube complex or any commensurating action.

## Ways it can fail on its own

A refutation needs one groupoid: a minimal effective ample `𝒢` with a continuous
`Z^k`-cocycle with AF kernel and an infinite Kazhdan group in `[[𝒢]]`. That single object
would refute `kazhdan-subgroups-of-brin-thompson-groups-are-finite`'s last hypothesis
list without saying anything about `nV` itself — which is what makes this a prerequisite
that can fail on its own, rather than a restatement of the target.

## Attempts

- **Lemma A (established here; standard).** For an AF groupoid `𝒦`, the topological full
  group `[[𝒦]]` is locally finite.
  *Proof.* Write `𝒦 = ⋃_n 𝒦_n` with `𝒦_n` elementary, open and increasing. A compact
  open bisection `U ⊆ 𝒦` is covered by the increasing open family, so `U ⊆ 𝒦_n` for some
  `n`; hence `[[𝒦]] = ⋃_n [[𝒦_n]]`. An elementary groupoid is a finite disjoint union of
  matrix groupoids `Z_j × (k_j × k_j)` over compact spaces `Z_j` (finitely many because
  the unit space is compact and the blocks are open). A full-group element preserves
  every `𝒦_n`-orbit setwise, so it preserves each block, and `[[𝒦_n]] = ∏_j C(Z_j,
  S_{k_j})` with `C` meaning locally constant maps. Finitely many such maps are constant
  on a common finite clopen refinement `Q`, so they generate a subgroup of the finite
  group `∏_{Q} S_{k_j}`. Hence each `[[𝒦_n]]`, and so `[[𝒦]]`, is locally finite. ∎
  *Corollary.* A Kazhdan subgroup of `[[𝒦]]` is finite, because property (T) forces
  finite generation (BdlHV Theorem 1.3.1) and a finitely generated locally finite group
  is finite. So (S_k) is trivially true when `c ≡ 0`, i.e. when `𝒢` itself is AF.

- **Lemma B (established here; first constraint on the hosts, 2026-09-18,
  e2-w2-nv-separate).** Let `𝒢 = 𝒢_1 × 𝒢_2` be a product of ample Hausdorff groupoids with
  compact unit spaces and let `c : 𝒢 → Z^k` be continuous with `ker c` AF. Then for every
  subgroup `Λ ≤ [[𝒢_1]]`, the subgroup
  `Λ_0 = {γ ∈ Λ : c(γ · 1_{𝒢_2}) ≡ 0 on the whole bisection}` is locally finite.
  *Proof.* `𝒢_2^{(0)}` is clopen in `𝒢_2` (open because `𝒢_2` is étale, closed because
  `𝒢_2` is Hausdorff), so `ℛ = 𝒢_1 × 𝒢_2^{(0)}` is a clopen subgroupoid of `𝒢` containing
  the unit space. `ker c ∩ ℛ = ⋃_n (𝒦_n ∩ ℛ)` and each `𝒦_n ∩ ℛ` is compact open,
  principal, with finite orbits, hence elementary; so `ker c ∩ ℛ` is AF. The elements of
  `Λ_0`, viewed as bisections of `ℛ`, lie in `ker c`, so `Λ_0 ≤ [[ker c ∩ ℛ]]`, which is
  locally finite by Lemma A. ∎
  *Consequence for the recorded hosts.* In `(M ⋊ Γ) × G_2` with `Γ = Z^3 ⋊ SL_3(Z)`, take
  `Λ = Γ`. `Γ` is a subgroup of `GL_4(Z)`, which is virtually torsion free by Minkowski's
  lemma (the level-3 congruence subgroup is torsion free), so every locally finite
  subgroup of `Γ` is finite. Hence **any** continuous `Z^k`-cocycle on the host with AF
  kernel has `{γ ∈ Γ : c_1(γ, ·) ≡ 0}` finite. In particular the canonical cocycle
  `(h, g) ↦ c_{G_2}(g)` is killed (its kernel contains all of `M ⋊ Γ`), and so is every
  cocycle that ignores the Kazhdan direction. A refuting host must carry a cocycle that
  is *almost faithful along its Kazhdan subgroup* — and, by the patching form of Lemma A,
  the same holds for every element of `[[𝒢]]` patched from finitely many partial
  translations on which `c` vanishes.

- **What Lemma B does not give.** It does not exclude a cocycle `c_1 : Γ × M → Z^k` with
  `c_1(γ, ·) ≢ 0` for all `γ ≠ 1`. Two further facts, recorded so that the next attempt
  does not rediscover them:
  - `ker c` is AF, so `C*(ker c)` is a unital AF algebra and therefore has a tracial
    state; hence `ker c` has an invariant Borel probability measure on the unit space.
    For `G_2^n` that measure is unique: the `(1/2,1/2)`-Bernoulli measure to the `n`-th
    power, the unique trace of `M_{2^∞}^{⊗n}`. So an AF-kernel cocycle forces an
    invariant measure for the kernel even when the groupoid itself has none. This is
    *not* contradicted by the hosts, which have no invariant measure for the whole
    groupoid.
  - The full group does **not** act on the set of `ker c`-invariant measures: conjugating
    `h ∈ ker c` by a bisection `U` gives `c(u h u'^{-1}) = c(u) + c(h) - c(u')`, and
    `c(u) ≠ c(u')` for different points of `U`. Only bisections with globally constant
    `c` normalize `ker c`. (Correctly so: `V = [[G_2]]` does not preserve the Bernoulli
    measure.) Any argument that pushes an invariant measure around with full-group
    elements dies here.
