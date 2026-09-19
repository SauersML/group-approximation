---
rg: 2
id: nv-brick-groupoid-and-kazhdan-host-are-both-o2
kind: claim
title: "The brick groupoid G_2^n of nV and the amenable Kazhdan hosts have the same reduced C*-algebra, namely O_2, and the same (vanishing) groupoid homology, so no C*-algebraic or homological invariant separates them"
distinct_from:
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that builds the host and kills the hypothesis list "ample, amenable, minimal, effective, purely infinite"; this computes the reduced C*-algebra of the host and of G_2^n and finds them isomorphic, which kills every hypothesis list formulated in invariants of that algebra, including K-theory, traces, the Cuntz semigroup and nuclear dimension.
  rs-boundary-groupoid-is-expansive-amenable-kazhdan-host: that kills compact generation and expansivity; this kills the whole operator-algebraic layer and reduces the remaining separation to a Cartan-pair (groupoid) question inside O_2.
  matui-groupoid-homology-kunneth-and-full-shift-vanishing: that is Matui's Kunneth formula and the homology of one-sided SFT groupoids; this applies it to the two specific groupoids and combines it with the C*-level computation into a class kill for nV.
  trivial-k-theory-kirchberg-algebras-are-o2: that is the UCT-equivalent question of whether every trivial-K-theory Kirchberg algebra is O_2; this does not use it, both isomorphisms come from Kirchberg's O_2-absorption theorem applied to an explicit tensor factorization.
artifacts: []
---

**Status: OPEN** (demoted 2026-09-18 at landing: referee lens 2 refuted Step 5 of
`nv-brick-groupoid-and-kazhdan-host-are-both-o2-proof`, and lens 3 refuted the gate
wording this node feeds into `brin-thompson-groups-nv-are-a-t-menable`. The route now
requires the open gap claim `kazhdan-host-crossed-product-is-simple-and-nuclear`, which
is the single import Step 5 needs. See `## Attempts`.)

**What is not in doubt.** All three lenses checked Steps 1-4 and 6-8 and found them
correct, so the statement below is expected to be true and the tensor-factorization
mechanism is intact. What is missing is one literature import, not a construction.

## Notation

- `C = {0,1}^N`, `σ` the one-sided full 2-shift, `G_2` its Deaconu–Renault groupoid in
  Matui's convention, so `[[G_2]] = V` and `nV ≤ [[G_2^n]]` (brick maps are exactly the
  finite unions of products of the basic bisections `U_{μ,ν}`).
- `𝒢_W1 = (M ⋊ Γ) × G_2` with `Γ = Z^3 ⋊ SL_3(Z)` acting freely, minimally and amenably on
  a Cantor set `M`: the host of `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`.
- `𝒢_RS = (Γ' ⋉ Ω) × G_2` with `Γ'` a Kazhdan `PGL_3` lattice on its Robertson–Steger
  boundary: the host of `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`.

## Statement

For every `n ≥ 1`,

1. `C*_r(G_2^n) ≅ O_2 ≅ C*_r(𝒢_W1) ≅ C*_r(𝒢_RS)`;
2. `H_*(G_2^n) = 0 = H_*(𝒢_W1) = H_*(𝒢_RS)` (Matui's groupoid homology, all degrees);
3. consequently `K_*(C*_r(·)) = 0`, there is no tracial state, the ideal lattice is
   trivial, the Cuntz semigroup is `{0, ∞}`, and the nuclear dimension is `1`, for all
   three groupoids alike.

## Consequence (class kill)

**Killed class.** Every proof of the shape

> `𝒢` is an ample groupoid whose invariants `P(C*_r(𝒢))` and `P'(H_*(𝒢))` are such and
> such, hence `[[𝒢]]` has the Haagerup property (or: its Kazhdan subgroups are finite),

where the hypotheses depend only on the isomorphism class of the reduced C*-algebra and
on the groupoid homology. Any such hypothesis satisfied by `G_2^n` is satisfied by
`𝒢_W1`, whose full group contains the infinite Kazhdan group `Γ`.

- **Invariant:** property (T) of `Γ`.
- **Step where every member dies:** the passage from an invariant of `C*_r(𝒢)`, or of
  `H_*(𝒢)`, to a statement about `[[𝒢]]`. The two groupoids have the *same* algebra, so no
  such passage can distinguish `2V` from a group containing `Γ`.
- **Scope.** This covers K-theory, K-theoretic classification data, traces and tracial
  states, the ideal lattice, the Cuntz semigroup, nuclear dimension, decomposition rank,
  Z-stability, strong self-absorption, quasidiagonality, the UCT, and Matui's HK-type
  invariants. It also kills the stronger-sounding hypothesis "`𝒢` is amenable and
  `C*_r(𝒢) ≅ O_2`".

## The gate

What survives at the operator-algebra level is exactly the **Cartan pair**. Both
groupoids are second countable, Hausdorff, ample, minimal and effective, so their
canonical diagonals are Cartan subalgebras and, by Renault's reconstruction theorem
(graph form: `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids`),

> `G_2^n ≅ 𝒢_W1` as topological groupoids **iff** there is an isomorphism
> `C*_r(G_2^n) → C*_r(𝒢_W1)` carrying `C(C^n)` onto `C(M × C)`.

Both sides of that isomorphism are `O_2`. So the entire remaining separation problem is:

> **are the two explicit diagonals `C(C^n)` and `C(M × C)` conjugate Cartan subalgebras
> of `O_2`?**

A surviving operator-algebraic proof for `nV` must therefore be *diagonal-sensitive*: it
must use the Cartan pair, never the algebra alone.

## Necessary prerequisite for the target (new decomposition)

`[[·]]` is a groupoid invariant, so an isomorphism `G_2^n ≅ 𝒢_W1` would give
`nV ≅ [[𝒢_W1]] ⊇ Γ`, an infinite Kazhdan subgroup. Hence

- `brin-thompson-groups-nv-are-a-t-menable` **implies** `G_2^n ≇ 𝒢_W1`, and equally
  `G_2^n ≇ 𝒢_RS`;
- a proof that the two groupoids *are* isomorphic refutes the target, and moreover
  answers Zaremsky Problem 2.7 on the negative side by exhibiting an infinite Kazhdan
  subgroup of `nV`.

By item 1 and item 2 no invariant currently recorded on the graph distinguishes them.
The first candidate that does is the `Z^n`-cocycle with AF kernel
(`brick-groupoid-has-zn-cocycle-with-af-kernel`,
`af-by-zk-full-groups-have-finite-kazhdan-subgroups`).

## Attempts

- **2026-09-18 (e2-w2-nv-separate, operator-algebras): the route
  `nv-brick-groupoid-and-kazhdan-host-are-both-o2-proof`, refuted at Step 5 by referee
  lens 2; kept as the attempt.** The proof factors each reduced algebra as (unital
  separable simple nuclear) `⊗ O_2` and applies Kirchberg's `O_2`-absorption theorem. The
  referee reasons, in their own terms:
  - **Lens 2 (refuted=true), the decisive one.** A quantifier inversion on the
    load-bearing import at Step 5. The Rørdam–Sierakowski sentence quoted verbatim is an
    **existence** statement — "`G` admits a free, amenable, minimal action on the Cantor
    set `X` such that `C(X) ⋊_r G` is a Kirchberg algebra […] iff `G` is exact and
    non-amenable" — i.e. there is *some* such action. Step 5 applies it as a universal to
    the host's specific `M`, and that `M` is **not** the Rørdam–Sierakowski action: it is
    constructed independently in Steps 1–3 of
    `amenable-purely-infinite-groupoid-kazhdan-host-proof` (a Zorn-minimal closed
    invariant subset of `X' × Z` with `X' ⊆ T^Γ`), and
    `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan` cites Rørdam–Sierakowski
    only under "Prior art and novelty", noting that "Steps 1–3 of the route reprove the
    free, amenable, minimal part". So the cited import says nothing about
    `C(M) ⋊_r Γ`. The properties Step 5 actually needs — unital, separable, **simple**,
    **nuclear** — are true for this `M`, but only via two theorems that appear nowhere in
    the route's `requires:` list or text: topological amenability of the action implies
    nuclearity of the reduced crossed product (Anantharaman-Delaroche), and free (hence
    topologically free) plus minimal implies simplicity of the reduced crossed product
    (Archbold–Spielberg). A third hypothesis mismatch sits in the same step:
    Rørdam–Sierakowski needs `Γ` **exact**, and Step 5 supplies property A
    (`commutative-ring-linear-groups-have-property-a`), while the host route's own
    re-referee note records that the property-A-to-exactness link was deliberately removed
    there; Ozawa's property A ⟺ exactness is cited nowhere.
    - **What it costs.** Item 1 for `𝒢_W1`, the Cartan gate below, and the *effective*
      form of the class kill, since `𝒢_W1` is the only host asserted effective —
      `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` explicitly lists "Not
      asserted: that `Γ'` acts topologically freely on `Ω`, i.e. that `R` is effective".
    - **What survives even under this lens.** Step 6 (`𝒢_RS`) is clean, since that node's
      item 4 states simplicity, nuclearity and pure infiniteness of `C(Ω) ⋊_r Γ'`
      directly. So the **weaker class kill** — *no invariant of `C*_r(𝒢)` or `H_*(𝒢)`
      separates `G_2^n` from* ***some*** *Kazhdan host* — stands as written. Only the kill
      for hypothesis lists that include effectiveness, and the Cartan-pair reduction, are
      lost until the gap closes.
    - **The fix named by the lens**, which is now
      `kazhdan-host-crossed-product-is-simple-and-nuclear`: drop the Rørdam–Sierakowski
      quote from Step 5 and cite the two standard theorems that deliver exactly "unital
      separable simple nuclear"; or redefine `M` to *be* the Rørdam–Sierakowski action,
      which costs re-deriving the host's properties 1–5 for it.
  - **Lens 1 (refuted=false)** and **lens 3 (refuted=false on this computation)** both
    read Step 5 as sound and accepted the Rørdam–Sierakowski appeal. Lens 3 checked Step 1
    independently and noted that it genuinely uses étaleness (counting measures on `𝒢_x`),
    so it would not survive a non-unimodular Haar system; lens 1 verified that
    `(⊕_x λ_x) ⊗ (⊕_y λ_y) = ⊕_{(x,y)} λ_x ⊗ λ_y` is genuine, since Hilbert tensor
    products distribute over arbitrary direct sums. Neither rebutted lens 2, so the
    finding stands unanswered.
  - **Checked and found correct by all three lenses**, and therefore not re-opened:
    Step 1 (`C*_r(𝒢 × ℋ) = C*_r(𝒢) ⊗_min C*_r(ℋ)`, from scratch), Step 3's statement of
    Kirchberg–Phillips `O_2`-absorption (unital simple separable nuclear, no UCT),
    Step 4's induction, Step 6, Step 7 (Künneth with
    `H_*(G_2) = coker(I-2) ⊕ ker(I-2) = 0`) and Step 8 (`K_*(O_2) = 0`, no trace, trivial
    ideal lattice, `Cu = {0, ∞}`, `dim_nuc = 1`).
- **Two loose ends recorded for whoever repairs this.**
  1. `brin-thompson-groups-nv-are-a-t-menable` records that the Robertson–Steger action is
     "not known to be topologically free", while
     `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` imports simplicity of
     `C(Ω) ⋊_r Γ'`, which for a *minimal* action forces topological freeness. Those two
     lines should be reconciled; if simplicity is trusted, `𝒢_RS` is effective after all
     and the effective form of the class kill is recoverable through Step 6 alone.
  2. The Künneth import is stated on the graph "for étale groupoids `𝒢` and `ℋ`", which is
     slightly over-quantified relative to Matui's totally-disconnected setting. It is
     applied here only to ample groupoids, so nothing downstream is affected.
