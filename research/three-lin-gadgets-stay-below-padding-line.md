---
rg: 2
id: three-lin-gadgets-stay-below-padding-line
kind: claim
title: Every gadget-certified reduction from 3Lin over a group of order q into a permutation 2-CSP on the same alphabet whose non-identity permutations fix at most one point -- Max-2Lin(Z_q), affine 2Lin over F_q, all of UG_3 -- has deficit ratio below 1 + (2q^2-q-2)/(3q^2) < 5/3, and all of UG_4 stays below 89/48; so none crosses the padding line
distinct_from:
  unique-games-np-hard-below-the-padding-line: that is the open milestone R > 2 for some unique-games point; this kills one proof family for it (per-gadget certified reductions from 3Lin(G) into Gamma-2CSPs on alphabet G with few fixed points) and leaves it open.
  ug-hardness-deficit-ratio-padding-line: that caps padded proper splits of d-to-d games by a completeness count; this caps gadget reductions whose input is 3Lin, dying at the soundness step against an anchored threshold adversary.
  twin-mixture-caps-deficit-ratio-of-local-amplifiers: that caps black-box maps whose input is already a unique game; this caps reductions whose input is 3Lin(G), which that node lists as a survivor ("direct reductions from 3LIN or label cover with non-split outputs").
  unique-games-hard-at-completeness-one-half: that is a proved hardness point with R < 2 reached through 2-to-2 games; this is an upper bound on what a different pipeline (3Lin gadgets) can certify.
artifacts:
  - experiments/ugc-affine-gadget-cap-2026-09-17/check_anchored_adversary.py
  - experiments/ugc-affine-gadget-cap-2026-09-17/results-2026-09-18.txt
---

**ESTABLISHED (class kill).** Proof: `three-lin-gadgets-stay-below-padding-line-proof`.
The proof is elementary. The script checks it with exact rationals:
exhaustively for `q = 2, 3` and on random edges for `q = 4, 5`. In every case
the bound of item 3 is attained.

## Setting

* **Alphabet and predicate.**
  * `G` is a finite set of size `q >= 2`, for example `Z_q` or `F_q`.
  * `H ⊆ G^r` with `r >= 2` is the satisfying set of one source constraint.
    Every pair of coordinates of `H` is uniform: for `p != p'`, the pair
    `(h_p, h_p')` is uniform on `G^2` when `h` is uniform on `H`.
  * Put `N = |H|`, so `q^2` divides `N`.
  * The main example is 3Lin: `H_b = {(u, v, w) : u + v + w = b}` over an abelian
    group of order `q`. Then `r = 3` and `N = q^2`.
* **Output constraints.** `Γ ≤ Sym(G)` is a permutation group. An output
  constraint is `z = γ(y)` with `γ ∈ Γ`: a unique-games constraint whose
  permutations are restricted to `Γ`. Let `f` be the largest number of fixed
  points of a non-identity element of `Γ`, and put `ρ = max(1, f)/q`.
  * Translations (Max-2Lin(Z_q)): `f = 0`.
  * Affine maps `x -> a x + c` on `F_q` (2Lin with coefficients): `f = 1`.
  * `S_3 = AGL(1, 3)` (all of `UG_3`): `f = 1`.
  * `S_4` (all of `UG_4`): `f = 2`.
  * `S_q`: `f = q - 2`.
* **Gadgets.** A *gadget* for `H` is a finite distribution on output
  constraints over three kinds of variable:
  * the primary variables `x_1, ..., x_r`;
  * local auxiliary variables;
  * optionally, global reference variables shared by all gadgets, such as a
    variable `z_0` standing for the value `0`.
* **Completeness.**
  * For `h ∈ H`, `best(h)` is the least fraction of violated constraints over
    assignments with `x = h` in which every reference variable takes its
    intended value.
  * The completeness is `c = max_h best(h)`.
* **Certified soundness.** Every such certificate is at most `s_rand` (item 1).
  * *Case analysis* (Trevisan--Sorkin--Sudan--Williamson style). For
    `ξ ∈ G^r` let `best(ξ)` be the least violated fraction with primaries `ξ`
    and references at their intended values. Put
    `s_cert = (1 - |H|/q^r) min_{ξ ∉ H} best(ξ) + (|H|/q^r) min_{ξ ∈ H} best(ξ)`.
    It is the deletion that the case analysis certifies against a source
    assignment satisfying a `|H|/q^r` fraction of constraints, which is the
    random-assignment value of a random-like instance.
  * *Random-on-primaries* (Håstad--Huang--Manokaran--O'Donnell--Wright
    style). `s_rand` is the least expected violated fraction over
    distributions of assignments whose primaries are uniform on `G^r`, with
    references at their intended values.
* **Deficit ratio.** The certified point `(1 - c, 1 - s)` of the output
  instance has deficit ratio `R = s/c`. The padding line is `R = 2`, as in
  `ug-hardness-deficit-ratio-padding-line`.

## Theorem

1. **Path bound.** Let `A` be a distribution of assignments `G^H -> G` with
   three properties:
   * it is `Γ`-equivariant: `A(γ ∘ y) = γ(A(y))`;
   * it is random on the primaries: the values `A(p_1), ..., A(p_r)` of the
     coordinate projections are uniform on `G^r`;
   * it sends every constant function `c` to `c`.

   Put `M(A) = max Pr[A(y) != A(y')]` over pairs `y, y'` differing at exactly
   one point of `H`. Then every gadget for `H` has
   `s_cert <= s_rand <= N M(A) c`.
2. **Anchors.**
   * An *anchor* is a function `γ ∘ p_j`.
   * Two distinct anchors agree on at most `ρ N` points of `H`.
   * Put `α0 N = ceil(N (1 + ρ)/2)`. A function agreeing with an anchor on
     more than `α0 N` points has exactly one such anchor.
   * A neighbour of such a function that also has more than `α0 N`
     agreements with some anchor has the same anchor.
3. **Anchored threshold adversary.**
   * *Decoder.* Let `(ξ, h*)` be jointly distributed, with `ξ` uniform on
     `G^r` and `h*` uniform on `H`. Put `D_j = [ξ_j != h*_j]`. Assume:
     * (H1) `Pr[D_j | h*] = δ_j` does not depend on `h*`;
     * (H2) given `h*` and `D_j`, `ξ_j` is uniform on `G \ {h*_j}`.
   * *Threshold.* Draw `t` uniform on `[α0, 1)`, independent of `(ξ, h*)`.
   * *Rule.* A function `y` is *near* if its largest anchor agreement exceeds
     `t N`.
     * A near `y` with anchor `γ ∘ p_j` gets `A(y) = γ(ξ_j)` when `D_j` holds.
     * Every other `y` gets `A(y) = y(h*)`.
   * *Guarantee.* `A` satisfies the hypotheses of item 1, and
     `N M(A) <= λ = 1 + δ (1 - 1/N)/(1 - α0) - δ/(q - 1)` with
     `δ = max_j δ_j`.
   * *Tightness.* The maximum is at an edge whose near endpoint has exactly
     `α0 N + 1` agreements. The script finds it attained in all six cases it
     runs.
4. **Decoders.** Both of the following satisfy (H1) and (H2).
   * *Trivial decoder.* Take `h*` uniform and independent of `ξ`. Then
     `δ = 1 - 1/q`.
   * *Information-set decoder.* Draw a random set `I` of coordinates such that
     `h -> h_I` is a bijection `H -> G^I`, independent of `ξ`, and let `h*` be
     the point with `h*_I = ξ_I`. Then `δ_j = (1 - 1/q)(1 - θ_j)` with
     `θ_j = Pr[j ∈ I]`.
5. **Consequences for `f <= 1`.** Here `ρ = 1/q`, `α0 = (q+1)/(2q)` exactly,
   and `λ = 1 + δ (2q - 1 - 2q/N)/(q - 1)`.
   * (a) *Universal cap.* Every pairwise-uniform `H` has `R <= 3 - 1/q - 2/N`.
     For `q = 2` this is `5/2 - 2/N`, the Hadamard cap.
   * (b) *3Lin(G).* Take `I` a uniform 2-subset of `{1, 2, 3}`, so
     `δ = (1 - 1/q)/3`. Then **`R <= 1 + (2q^2 - q - 2)/(3q^2) < 5/3`** for
     every `q`, in each of these cases:
     * gadgets into Max-2Lin(Z_q);
     * gadgets into affine 2Lin over `F_q`;
     * gadgets into all of `UG_3` (`q = 3`, where the bound is `40/27`).

     The values are `4/3`, `40/27`, `37/24`, `118/75` and `236/147` for
     `q = 2, 3, 4, 5, 7`.
   * (c) *kLin.* Take `H = {x_1 + ... + x_k = b}` with `k >= 3`, and `I` a
     uniform `(k-1)`-subset. Then `R < 1 + (2q - 1)/(kq) < 1 + 2/k`.
   * (d) *Kill condition.* Any `H` with an information-set distribution of
     `min_j θ_j >= (q - 1)/(2q - 1)` has `R < 2`.
6. **More fixed points (3Lin, general `ρ`, same decoder).**
   * *All of `UG_4`.* Take 3Lin over a group of order 4 into `S_4`. Then
     `f = 2`, `ρ = 1/2`, `α0 = 3/4` and `R <= 89/48 ~ 1.854`.
   * *`A_5`.* 3Lin over `Z_5` into constraints from the alternating group
     `A_5` has `f = 2`, so `R <= 194/105 ~ 1.848`.
   * *`UG_5` is not covered.* For `S_5` (`f = 3`) the adversary gives only
     `166/75 ~ 2.213`. For `S_6` it gives `277/108 ~ 2.565`. So all of `UG_q`
     with `q >= 5` is **not** killed.

## Class kill, stated as invariant and step

* **Class.** Reductions of the following kind:
  * the source is Gap-3Lin(G) with `|G| = q`, or any source whose constraint
    sets are pairwise uniform and have an information-set distribution
    meeting item 5(d);
  * each source constraint is replaced by a local gadget whose primaries are
    the source variables, with shared reference variables allowed;
  * the output alphabet is `G` itself, and the permutations generate a group
    `Γ` meeting item 5 or 6;
  * the NO case is certified per gadget, by `s_cert` or `s_rand`.

  This includes the classical 3Lin-to-2Lin gadget pipeline for every `q`,
  and every `q`-ary Håstad-type composition that stops at a
  `(1 - ε, 1/q + ε)` 3Lin instance.
* **Invariant.** Pairwise uniformity of `H`. It makes distinct anchors agree
  on at most `ρ N` points, so the anchor of a function is unique above
  `(1 + ρ)N/2`. It also lets two of the three coordinates decode `h*`
  exactly.
* **Step where every member dies.** Soundness. The anchored threshold
  adversary is a legal NO-side completion, meaning it is random on the
  primaries and fixes the references. Its expected deletion is at most
  `λ c`, and `λ < 2`.

## What this changes

* The two graph nodes that left this family open are
  `twin-mixture-caps-deficit-ratio-of-local-amplifiers` and the Attempts
  section of `unique-games-np-hard-below-the-padding-line`. Both named
  "direct reductions from 3LIN ... with non-split outputs" as a survivor.
  * For gadget-certified reductions on the source alphabet into
    Max-2Lin(Z_q), affine 2Lin, `UG_3`, `UG_4` or `A_5`-constraints, that
    survivor is dead.
  * The cap `5/3` holds uniformly in `q`. So letting `q` grow does not help:
    the deficit ratio of these pipelines stays bounded away from `2`.
* It generalises the Hadamard analysis from the boolean case to every `q` and
  every `Γ` with few fixed points. At `q = 2` the constant `1 + δ(3 - 4/N)`
  reappears as the case `ρ = 1/2`.
* The best previously recorded point, O'Donnell--Wright with `R = 5/4`
  (quoted in `unique-games-np-hard-below-the-padding-line`), is consistent
  with this cap.

## Survivors

1. **Large fixed-point groups.** Full `UG_q` for `q >= 5`, or any `Γ` whose
   non-identity elements can fix many points. Here the adversary's
   uniqueness radius `(1 + ρ)/2` is too close to `1`.
2. **Alphabet blow-up.** Outputs over an alphabet `L > q`, such as long-code
   or label-cover compositions whose labels are functions, not source
   values.
3. **Predicates with small information sets.** Examples are Hadamard-type `H`
   with many primaries, and more generally any `H` where every information
   set misses most coordinates, so that `θ < (q-1)/(2q-1)`. The Hadamard
   family has this shape.
4. **Global, non-local certificates.** NO-side arguments that are not per
   gadget, such as Fourier analysis over the whole composed instance, as in
   O'Donnell--Wright and the 2-to-2 proof.
