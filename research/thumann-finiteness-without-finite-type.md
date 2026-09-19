---
rg: 2
id: thumann-finiteness-without-finite-type
kind: claim
title: Thumann's operad groups are of type F_n without finite type; infinitely many elementary classes are harmless once the splitting categories of large elementary classes are (n-2)-connected, so finite presentation needs only connected splittings
distinct_from:
  thumann-operad-groups-need-only-f-infinity-transformations: that weakens the hypothesis on the transformation groups (F_infinity instead of F_infinity-plus) and keeps finite type; this removes finite type and replaces it by a connectivity condition on splitting categories.
  non-lcm-dissection-operad-groups-are-f-infinity: that specializes Thumann's theorem, with a finite spine, to dissection operads; this allows an infinite spine.
  oligomorphic-operads-have-f-infinity-groups: that conjectures finiteness for operads with infinitely many elementary moves permuted oligomorphically; this proves its connectivity gate (c) under the splitting condition (G).
  bounded-refinement-operads-reduce-to-their-carriers: that shows operads with bounded refinement depth add nothing beyond Zaremsky actors; this is the finiteness theorem for the complementary, unbounded regime.
---

**ESTABLISHED** (lane bh-invent-07, 2026-09-18). This is a lane proof that modifies one estimate of
Thumann's proof; one referee PASS (bh-ref-engines, 2026-09-18). The source is W. Thumann, *Operad groups
and their finiteness properties*, arXiv:1409.1085, read in its LaTeX source. Line numbers below
refer to that file. No priority is claimed, and no literature search was done beyond the source.

## Setting

`𝒪` is a planar, symmetric or braided operad with transformations. It has finitely many colors,
is color-tame (Def. `77101`, l.2656) and satisfies the cancellative calculus of fractions. We use
Thumann's notions of very elementary, elementary and strictly elementary transformation classes
(Defs. `13449`, `24121`, l.2077–2094). The elementary classes form the spine of the poset of
higher-degree classes (Def. `79040`, Construction `45209`). `Γ = π_1(𝒪, X)`.

**The splitting category.** Let `Θ` be a strictly elementary class, and fix `θ ∈ Θ` with input
word `K` and output `c`. `𝒜(Θ)` is the poset of proper *elementary pre-factorizations* of `θ`,
that is, factorizations `θ = β_1 β_2` in `𝒰/𝒢` with:
- `β_1 : K → L` an elementary arrow: a tensor of elementary operations and identities, with at
  least one higher-degree operation;
- `β_2 : L → c` not a transformation, so `deg L ≥ 2`.

The order is refinement: `(L, β_1) ≤ (L', β_1')` if `β_1' = β_1 δ`. Up to isomorphism `𝒜(Θ)`
depends only on `Θ`. It is the category `𝒜_i` in the proof of Lemma `15097` (l.4428), where
Thumann shows it is nonempty.

**Splitting conditions.**
- **(G)_n**: there is `D_n` such that `𝒜(Θ)` is `(n − 2)`-connected for every strictly elementary
  class `Θ` of degree at least `D_n`. Here `n ≥ 2`.
- **(G)_∞**: `(G)_n` holds for every `n`. In other words, the connectivity of `𝒜(Θ)` tends to
  infinity as `deg Θ → ∞`.

If `𝒪` has finite type, the strictly elementary classes have bounded degree, so `(G)_∞` holds
vacuously.

## Statement

**Theorem.** Let `𝒪` be as above, finitely generated (finitely many very elementary classes), and
let `n ∈ {2, 3, …, ∞}`. Suppose `ℐ(𝒪)` is of type `F_n` and `(G)_n` holds. Then every operad
group `π_1(𝒪, X)` is of type `F_n`.

In particular, `π_1(𝒪, X)` is **finitely presented** as soon as `ℐ(𝒪)` is finitely presented and
the splitting categories of all but finitely many degrees of strictly elementary classes are
**connected**. **No bound on the spine is needed.**

**Variant (infinitely many moves).** Drop finite generation. Assume instead:
- **(VE)** very elementary classes have bounded degree `m_V`;
- **(Cc)_n** each `(𝒰/𝒢)_k` has finitely many `Γ`-orbits of cells of dimension at most `n`;
- **(St)_n** cell stabilizers are of type `F_n`.

Then `(G)_n` still implies that `Γ` is of type `F_n`. For a finitely generated operad,
(Cc)_n holds by Thumann's argument at l.3784–3833, which uses only that there are finitely many
very elementary classes and finitely many colors. (St)_n holds when `ℐ(𝒪)` is of type `F_n`, by
`thumann-operad-groups-need-only-f-infinity-transformations`, whose finite-orbit argument works
for `F_n` in the same way.

## Proof

Everything is Thumann's proof of Theorem `41762` (l.2664), except one estimate.

1. **Brown's criterion.**
   - `𝒰/𝒢` is contractible. The subsection "A contractible complex" (l.3196–3623) uses only the
     cancellative calculus of fractions.
   - The degree filtration is cocompact and has `F_n` stabilizers, by (Cc)_n and (St)_n.
   - So `Γ` is `F_n` once the pairs `((𝒰/𝒢)_k, (𝒰/𝒢)_{k−1})` are `n`-connected for large `k`.
     Then `(𝒰/𝒢)_k` is `(n − 1)`-connected and cocompact (Thm `46200`, l.2689, and its `F_n` form).
     Attaching along an `(n − 1)`-connected descending link gives an `n`-connected pair (Lemma
     `76169`, l.1027). So it suffices that `lk↓(𝒦)` is `(n − 1)`-connected for all objects `𝒦` of
     large degree.
2. **Whole link = corona.** `lk↓(𝒦) ≃ Corona(𝒦)`, the full subcategory of elementary arrows out of
   `𝒦`. This is Prop. `29625` with Lemma `90173` (l.4529–4600). It uses only the defining property
   of the spine, which holds for the spine of any graded poset (Construction `45209`).
3. **Core.**
   - `Core(𝒦) ≅ 𝒜𝒞_d(C, A; T)` (Prop. `19549`, l.3902).
   - The archetype set `A` is infinite in general, as Thumann notes. It is tame (color-tame) and of
     bounded length `m_V`.
   - So Theorem `85504` (l.2921) gives connectivity `ν_d(deg 𝒦)`, which tends to infinity.
4. **Corona from core: the one change.**
   - Build `Corona(𝒦)` from `Core(𝒦)` with the Morse function
     `f(𝒴, α) = (#_se^N(α), …, #_se^2(α), deg 𝒴)`, ordered lexicographically, where
     `N = deg 𝒦`. For fixed `𝒦` only degrees up to `N` occur, so this is Thumann's function with
     `m_E` replaced by `N`. Its values are well ordered, and objects with equal values are
     independent.
   - **Mixed objects** have contractible descending links (Lemma `65633`, l.4195). No finiteness
     is used there.
   - **Pure objects.** Let `(𝒴, α)` be pure: `α` consists of `𝔫 ≥ 1` strictly elementary
     operations `θ_i` of degrees `d_i`, and `𝔩 = N − Σ d_i` identities. Thumann shows (l.4428–4460)
     that `lk↓(𝒴, α)` is the join of two parts:
     - the Grothendieck join `𝒜(θ_1) ∘ ⋯ ∘ 𝒜(θ_𝔫)`, which realizes to a topological join (l.985);
     - an arc complex on the identities, with connectivity at least `max(−2, ν_d(𝔩))`. In the
       planar case this is Thumann's bound over identity components.
   - Write `c_i` for the connectivity of `𝒜(θ_i)`. Joins add connectivity plus 2, so
     `conn lk↓(𝒴, α) ≥ Σ_i (c_i + 2) − 2 + max(−2, ν_d(𝔩)) + 2 ≥ Σ_i (c_i + 2) − 2.`
   - Thumann uses only `c_i ≥ −1`, and then needs `𝔩 ≥ N − 𝔫 m_E`. **This is the only place
     where finite type enters the proof.**
5. **The estimate under (G)_n.**
   - If some `d_i ≥ D_n`, then `c_i ≥ n − 2`, and the bound gives `conn ≥ n − 2`.
   - Otherwise every `d_i < D_n`. If also `conn < n − 2`, then:
     - `Σ_i (c_i + 2) ≤ n` with each term at least 1, so `𝔫 ≤ n`;
     - hence `𝔩 ≥ N − n D_n`, so `ν_d(𝔩) ≥ n` once `N` is large;
     - then `conn ≥ 𝔫 + ν_d(𝔩) ≥ n + 1`, a contradiction.
   - So every descending link in the build-up is `(n − 2)`-connected for large `N`.
     - By Lemma `76169` each attachment is an `(n − 1)`-connected pair, so the pair
       `(Corona(𝒦), Core(𝒦))` is `(n − 1)`-connected.
     - `Core(𝒦)` is highly connected, so `Corona(𝒦)` is `(n − 1)`-connected for large `N`, and so
       is `lk↓(𝒦)`, by step 2.
   - For `n = ∞`, run this for every `n`.
6. **Variant.** Steps 2–5 use only (VE) and the three standing assumptions. Step 1 uses exactly
   (Cc)_n and (St)_n. `∎`

## Calibration

- **Finite type (Thumann).** Condition (G) is vacuous, and this recovers Theorem `41762`, with
  `F_∞` transformations by the Thumann node above.
- **Röver–Nekrashevych groups.** Finite type, one very elementary class.
- **Twisted Brin–Thompson groups `SV_G`**, for `G` oligomorphic on `S`. This is the Variant:
  - the very elementary classes are the splits `θ_s`, of degree 2;
  - (Cc)_n and (St)_n are the analogues, for Thumann's complex, of Belk–Zaremsky's
    cocompactness and stabilizer computations for their Stein complex (arXiv:2001.04579,
    `prop:cocpt`, `prop:stabs`), under their hypotheses. The orbit count for Thumann's complex
    was not written out here, so this item is a consistency check, not a new proof;
  - the strictly elementary classes are the full splits `θ_C` in finite color sets `C`, of degree
    `2^{|C|}`;
  - `𝒜(θ_C)` is the open interval of the corresponding Stein interval. Coarsenings of an
    elementary partition are elementary (BZ §5), so `β_1` is automatically elementary. By
    `stein-complex-elementary-intervals-are-grid-spheres`, that interval is `≃ S^{|C|−2}`. So
    `(G)_n` holds with `D_n = 2^{n+1}`;
  - the theorem therefore recovers BZ's `thm:FinitenessTheorem` (oligomorphic action with `F_n`
    finite-set stabilizers gives `SV_G` of type `F_n`).

  Its infinite spine and its "log" connectivity bound are exactly the phenomenon (G) isolates.

## Consequences

1. **The closed-MCG host.** `closed-mcg-bh-via-edge-split-operad` needs two things of the
   edge-split operad `𝒪_E`: Ore's condition, and a finite spine
   (`edge-split-operad-satisfies-ore`).
   - `𝒪_E` is finitely generated, has one color, and has finite transformation groups.
   - So by the Theorem with `n = 2`, **the finite spine can be replaced by: the splitting
     category of every spine element of large degree is connected**. For `F_∞`, replace it by
     `(G)_∞`.
   - The Boone–Higman conclusion needs only finite presentation, so `n = 2` suffices.
   - The condition is local: one finite poset per spine element. It can be tested on the spine
     elements already found (at least 16, bh-free-54).
   - It fails only if large spine elements have disconnected splittings, as for a full split in
     just two colors, `𝒜 ≃ S^0`.
2. **The unbounded regime.**
   - By `bounded-refinement-operads-reduce-to-their-carriers`, operadic hosts can go beyond
     Zaremsky actors only when refinement depth is unbounded, that is, when elementary classes of
     unbounded degree occur.
   - The Variant shows finiteness survives there, under (VE), (Cc), (St) and (G).
   - This settles the connectivity gate (c) of `oligomorphic-operads-have-f-infinity-groups`
     under (G). There, (O1) and (O2) are meant to supply (Cc) and (St), which is still only a
     lane sketch.

## Scope

- The proof establishes sufficiency only. Nothing here shows that (G) is necessary for finite
  presentation.
- Without (G) the method says nothing. A class of every large degree whose splitting category is
  two points would break the corona estimate. That leaves the finiteness of the operad group
  undecided, not refuted.
- The `F_n` form of Brown's criterion and of the stabilizer argument are standard adaptations of
  the `F_∞` versions the source uses. They are not written out in the source.

## Lesson for general BH

**Finite type is a connectivity device, not a finiteness hypothesis.** In Thumann's engine the
three finiteness inputs separate cleanly:
- cocompactness comes from finitely many very elementary moves (or from orbit finiteness);
- stabilizers come from the transformation groups;
- high connectivity comes from **how large elementary classes split**.

Finite type makes the last input vacuous. The grid spheres of twisted Brin–Thompson groups, the
engine behind Conjecture H, are the same input met head-on.

So Thompson-like hosts with infinitely many minimal common refinements are not blocked by their
infinite spines. This covers the non-LCM dissection hosts behind closed mapping class groups and
Deligne's lattice, and the unbounded-refinement operads, which are the only ones that can beat
twisted Brin–Thompson groups. The finiteness gate becomes a **local homotopy test on each
elementary class**: finite presentation needs only that the splitting categories of large
elementary classes are connected.

## Referee (bh-ref-engines, 2026-09-18): PASS

I checked this against Thumann's proof of Lemma `15097` in his source (l.4428–4475).
- **Where finite type enters.** For a pure object, Thumann bounds the connectivity of the descending link by
  `𝔫 + ν_d(𝔩)`, using `𝔫 m_E + 𝔩 ≥ deg 𝒦`.
  - This comes from the up-link, which is the join of the `𝒜_i`, each only nonempty, so `(𝔫−2)`-connected.
  - The down-link is `ν_d(𝔩)`-connected.
  - Finite type enters exactly there, and through `m_E` in the Morse function. The node locates this
    correctly.
- **The replacement bound is correct.** `conn ≥ Σ(c_i + 2) − 2 + (max(−2, ν_d(𝔩)) + 2)`, by joins.
  - The case split under `(G)_n` is correct.
  - If some `d_i ≥ D_n`, then `conn ≥ n − 2`.
  - Otherwise `𝔫 < n`, so `𝔩 ≥ N − nD_n`, and then `conn ≥ 𝔫 + ν_d(𝔩) ≥ n + 1`.
  - So `(Corona, Core)` is `(n−1)`-connected, and `lk↓` is `(n−1)`-connected for large `N`.
  - Replacing `m_E` by `N = deg 𝒦` in the Morse function is harmless for fixed `𝒦`.
  - The indices as corrected in 5a7d8353eb are right.
- **Identification.** Thumann's `𝒜_i` is the node's `𝒜(θ_i)`. Every proper elementary pre-factorization of
  a strictly elementary `θ_i` lowers `#_se^(d_i)`, so it is descending.
- **Imported, not re-checked here:**
  - the core connectivity `ν_d` for an infinite, tame archetype set of bounded length (Thm `85504`);
  - the variant's (Cc)_n and (St)_n;
  - the `F_n` forms of Brown's criterion and of the stabilizer argument.

  The node says these are standard adaptations.
- **The `SV_G` calibration** is correctly labelled a consistency check.

**Credit.** Thumann (arXiv:1409.1085). Brown's criterion and the Stein–Farley descending-link method.
Belk–Zaremsky (arXiv:2001.04579) for the twisted Brin–Thompson finiteness theorem it recovers.
