---
rg: 2
id: lifted-thompson-t-shift-template-area-is-a-stabilizer-function
kind: claim
title: "The cross-commutator area of the triple-shift template in T-bar is exactly the commutation area of one stabilizer word, so the template dies for all words as soon as one function on C(c) ∩ C(c_K) modulo <c, c_K> is proper"
distinct_from:
  lifted-thompson-t-template-envelope-contains-shift-graphs: that builds the Sh_3 template, shows it passes every element-level test, and leaves the word-level area question over a whole graph of vertex words; this rewrites that question, arc by arc and exactly, as the value of one function f on the single group D = C(c) ∩ C(c_K), and shows that the arcs out of any one vertex force infinitely many classes of D/<c,c_K>.
  lifted-thompson-t-conjugate-template-codes-have-bounded-cliques: that bounds k at the element level through annular localization of [y,h] for a varying element y; here the conjugated element is the fixed element c, so localization is empty, and the content sits in the word delta alone.
  bounded-area-commuting-conjugator-localization: that is the group-independent diagram lemma for Area([y,h]); this is a T-bar consequence and a refinement at fixed y, and it shows f is strictly finer than the localization data (f(c_K^q) = O(1) while the localization function a(c_K^q) is unbounded).
artifacts:
  - research/lifted-thompson-t-shift-template-stabilizer-function-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-thompson-t-shift-template-stabilizer-function-proof`.

## Setting

This is the template of `lifted-thompson-t-template-envelope-contains-shift-graphs`, item 2:

- `c = c_I` and `h = c_{sK}`;
- `s ∈ F`, with `σ` a fixed word for `s`;
- `t_v ∈ F` for `v = (i,j,l)`, sending `sI, sK, K` affinely onto `alpha_l, E_j, E_i`;
- `u_v` is an arbitrary word for `t_v`.

Fix a finite presentation of `T̄` and write Area for its area.  Put

```text
kappa = σ^(-1) h σ          (a fixed word for c_K),
D     = C(c) ∩ C(c_K) ⊂ T̄,  in which c and c_K are central,
f(d)  = min { Area([δ c δ^(-1), kappa]) : δ a word for d },     d ∈ D.
```

Every value of `f` is finite, because `dcd^(-1) = c` and `[c, c_K] = 1`.

## Statement

1. **(Exact per-arc identity.)**  Take an arc `a = (i,j,l) -> b = (j,l,m)` and put
   `δ_ab = σ^(-1) u_a^(-1) u_b`.  This is a word for
   `d_ab = s^(-1) t_a^(-1) t_b`, and `d_ab ∈ D` fixes `I ∪ K` pointwise.  Then

   ```text
   Area([C_b, H_a]) = Area([δ_ab c δ_ab^(-1), kappa])  >=  f(d_ab).
   ```

2. **(Invariance.)**  `f(c_K^p d c^q) = f(d)` for all integers `p, q`.  So `f` is a function
   on `D / <c, c_K>`.
3. **(Forced infinitude on one out-star.)**  Fix `a = (i,j,l)` and any choice of the `t`'s.
   The classes of `d_{a,(j,l,m)}` in `D/<c,c_K>`, for `m > l`, are pairwise distinct.  The
   class invariant that separates them is the interval `d(sI)`, which equals
   `s^(-1) t_a^(-1)(alpha_m)`.  These intervals lie in `[0, 5/16)`, where `c` and `c_K` act
   trivially, so they do not change under `d -> c_K^p d c^q`.
4. **(Kill criterion.)**  Call `f` *interval-proper* if it is unbounded on every set of
   elements of `D` whose images `d(sI)` are pairwise distinct.  If `f` is interval-proper,
   then the Sh_3 template violates (CCC2) at a single vertex, for every choice of words `u_v`
   and of the free parts of the `t_v`.  In fact the supremum of `Area([C_b,H_a])` over the
   out-arcs of one vertex is already infinite.  Properness of `f` on `D/<c,c_K>` is enough.
5. **(Upper bound; what `f` is not.)**  Put
   `a(d) = min_δ Area(δcδ^(-1)c^(-1))` and `b(d) = min_δ Area(δ^(-1) kappa δ kappa^(-1))`.
   Then `f(d) <= 2 min(a(d), b(d)) + A_1`, with `A_1 = Area([c, kappa])`, and the same holds
   after replacing `d` by any `c_K^p d c^q`.  In the other direction, `f(c_K^q) <= A_1` for
   every `q`, while `a(c_K^q) -> infinity` by `bounded-area-commuting-conjugator-localization`.
   So `f` is not controlled by the localization functions `a` and `b`.

## What this changes

- **Decomposition of the last hole of the template.**  The Dehn question left by wave 19 is
  "is `sup Area([kck^(-1),h])` finite over the Sh_3 arcs, for some system of vertex words?"
  It involves a whole compatible system of words, one per vertex.  The kill half of that
  question now reduces to one statement about one group:

  ```text
  (P)  f is interval-proper on D = C(c_I) ∩ C(c_K) ⊂ T̄.
  ```

  If (P) holds, the explicit shift template is dead for all words.  If (P) fails, the
  failure is an infinite family `d_n` whose words `δ_n` commute `δ_n c δ_n^(-1)` with
  `kappa` in bounded area.  That family is the only raw material from which a bounded-area
  template, and so by `lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear` a proof that
  `T` is not hyperlinear, could be built.
- **Consistency with the wave-19 class kill.**  Wave 19 showed that no invariant of the pair
  data `(C_v, H_v)` can kill the template.  `f` is not pair data.  It is a function of the
  single element `d`, computed by minimising over all its words, and it records how
  expensively a word for `d` witnesses the commutation `[dcd^(-1), c_K] = 1`.  So (P) is not
  covered by that obstruction, and there is no conflict.
- **Status of (P).**  (P) is OPEN.  The partial facts are recorded under `## Attempts`.
  `lifted-thompson-t-is-not-mf` stays OPEN.

## Attempts

- **2026-09-20 (swarm-0917-w20-w20-ptm-follow, host-geometry): towards (P).**  Nothing below
  is a proof.
  - *Folded diagrams.*  Suppose a minimal diagram for `[δcδ^(-1), kappa]` folds each
    `δ`-segment completely onto its partner `δ^(-1)`.  Gluing its `kappa` sides gives an
    annulus between two copies of `c`.  Then the `kappa` path reads `δ g δ^(-1)`, with `g` a
    short word for `c_K`, so `b(d)` is at most the area plus `O(1)`.  In this case `f`
    dominates `b` up to constants, up to right multiplication by `<c>`.  The general case has
    2-cells between the two hairs, and that is where all of the difficulty lies.
  - *Length alone cannot work.*  Take `δ = kappa^p δ_0 c^q`.  Its length is unbounded, but
    `f` does not change (item 2).  So no bridge count that uses only the lengths of the
    `δ`-segments can prove (P).  A proof has to work modulo `<c, c_K>`, and it has to use the
    positions `d(sI)`, which lie in `[0, 5/16)`.  Those positions are the only place where the
    shift structure enters (item 3).
  - *Homological shadow.*  In the relation module the arc chains are
    `D_e(γ_b - γ_a) + (1-H) g_b γ(c) - (1-C) g_a γ(h)`, with `D_e = (1-H_j)(1-C_l)`.
    Changing words is `γ_v -> γ_v + ∂q_v`.  So (P) has a dual certificate: a family of
    quasi-cocycles `ψ_e` that is balanced at each vertex.  Same-index 4-cycles give only
    trivial constraints.  No certificate has been found.
