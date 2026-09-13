# Thompson's group F: which non-amenability certificates can exist

Lane `z2-01-f-nonamenable` (Zaremsky Problem 2.1, root `zaremsky-2-01-thompson-f-amenable`),
2026-09-13. Part 1. This artifact kills two natural certificate classes for non-amenability
of `F`, sharpens a third, and records the C*-simplicity reformulation as a certificate class.
It decides nothing about amenability of `F`.

Notation. `F` acts on `[0,1]` by orientation-preserving PL homeomorphisms with dyadic
breakpoints and slopes powers of 2. `x_0` is the generator with `x_0(t) = t/2` on `[0,1/2]`,
`x_0(t) = t - 1/4` on `[1/2,3/4]`, `x_0(t) = 2t - 1` on `[3/4,1]`. For `c ∈ (0,1)` write
`F_[c,1] = { f ∈ F : f(t) = t for all t ∈ [0,c] }` and `F_[0,c] = { f ∈ F : f(t) = t for all
t ∈ [c,1] }`. A Schreier graph is *amenable* when it has Følner sets: finite `A` with
`|{(s,u) : s ∈ S, u ∈ A, su ∉ A}| / |A|` arbitrarily small.

## 1. Theorem A: end-rigid Schreier graphs are amenable

**Theorem A.** Let `S` be a finite symmetric generating set of `F`, `Y` an `F`-set and
`y ∈ Y`. Suppose `F_[c,1] ⊆ Stab_F(y)` for some `c ∈ (0,1)`, or `F_[0,c] ⊆ Stab_F(y)` for some
`c ∈ (0,1)`. Then the Schreier graph of the orbit `F·y` with respect to `S` is amenable.
More precisely, either the orbit is finite, or for every `M` there is `A ⊆ F·y` with
`|A| = M` and at most `sum_(s ∈ S) |k_s|` pairs `(s,u)` with `su ∉ A`, where `k_s` is defined
below.

*Proof.* Assume `F_[c,1] ⊆ Stab_F(y)`; the other case follows by conjugating with the flip
`t ↦ 1 - t`, which normalizes `F`.

Step 1 (germs at 0). Each `s ∈ S` fixes `0` and has finitely many breakpoints, so there are
`k_s ∈ Z` and `ε_s ∈ (0,1/2]` with `s(t) = 2^(k_s) t` for `t ∈ [0, ε_s]`. Put
`K = max_s |k_s|`.

Step 2 (x_0-powers near 0). `x_0` is increasing with `x_0(t) < t` on `(0,1)`, so
`x_0^j(c) → 0` as `j → ∞`, and `x_0^j([0,c]) = [0, x_0^j(c)]`. On `[0,1/2]`, `x_0` is `t ↦ t/2`.
Choose `N ≥ K` so large that `x_0^(N-K)(c) ≤ 2^(-K) min_s ε_s`. Then for `n ≥ N`,
`t ∈ [0,c]` and `s ∈ S`:
- `x_0^n(t) ≤ ε_s`, so `s(x_0^n(t)) = 2^(k_s) x_0^n(t)`;
- with `m = n - k_s ≥ n - K ≥ N - K`, all points `x_0^j(t)` with `j ≥ N - K` lie in
  `[0,1/2]`, where `x_0` halves. If `k_s ≥ 0`, `x_0^n(t) = x_0^(k_s)(x_0^m(t)) = 2^(-k_s)
  x_0^m(t)`. If `k_s < 0`, `x_0^m(t) = x_0^(-k_s)(x_0^n(t)) = 2^(k_s) x_0^n(t)`. Either way
  `x_0^m(t) = 2^(k_s) x_0^n(t)`.

Hence `s x_0^n = x_0^(n - k_s)` on `[0,c]`, i.e. `r_(s,n) := x_0^(-(n - k_s)) s x_0^n` is the
identity on `[0,c]`, so `r_(s,n) ∈ F_[c,1] ⊆ Stab_F(y)`.

Step 3 (the Følner sets). For `n ≥ N` and `s ∈ S`,
`s · (x_0^n y) = x_0^(n - k_s) r_(s,n) y = x_0^(n - k_s) y`.
- If the points `x_0^n y` (`n ∈ Z`) are pairwise distinct, set
  `A_M = { x_0^n y : N + K ≤ n < N + K + M }`. Then `|A_M| = M`, and `s·(x_0^n y) ∉ A_M` only
  if `n - k_s` leaves the window, which happens for at most `|k_s|` values of `n`.
- If `x_0^p y = y` for some `p ≥ 1`, the set `O = { x_0^n y : n ∈ Z }` is finite and every
  element of it is `x_0^n y` with `n ≥ N`. So `sO ⊆ O` for all `s ∈ S`. Since `S` generates
  `F`, `O = F·y` and the orbit is finite. ∎

**Corollary A1 (orbital certificates).** For every `t ∈ (0,1)` and every finite symmetric
generating set `S`, the Schreier graph of `F·t ⊂ (0,1)` is amenable: `F_[c,1] ⊆ Stab_F(t)`
for any `c ∈ [t,1)`. The same holds for the action on finite subsets of `(0,1)` (a finite set
`E` is fixed by `F_[c,1]` once `c ≥ max E`), and for every coset space `F/H` with `H`
containing some `F_[c,1]` or `F_[0,c]`.

**Consequence.** A non-amenable Schreier graph of `F` (which would prove non-amenability,
since an invariant mean on `F` pushes forward to an invariant mean on any `F`-set, and a
bounded-degree graph with an invariant mean has Følner sets) must come from a coset space
`F/H` where `H` contains no rigid stabilizer of an end interval. In particular no Ponzi
scheme (bounded-displacement 2-to-1 map) on an orbit of points, or of finite configurations
of points, of `(0,1)` exists. The mechanism is that near an endpoint every element of `F`
acts as a power of `x_0`, so long `x_0`-rays toward `0` are almost invariant.

**Scope and novelty.** Elementary; very likely folklore (Kaimanovich's non-Liouville proof
uses the same Schreier graphs, arXiv:1602.02971). No novelty is claimed. What is recorded is
that this certificate class is empty.

## 2. Theorem B: the orbit relation on the interval is hyperfinite

Let `R_F = { (t, f(t)) : t ∈ (0,1), f ∈ F }` and let `Aff` be the countable group of maps
`t ↦ 2^k t + d` (`k ∈ Z`, `d ∈ Z[1/2]`) of `R`. `Aff ≅ Z[1/2] ⋊ Z` is solvable, hence
amenable. Write `R_Aff` for its orbit relation on `R`.

**Theorem B.** (1) `R_F = R_Aff ∩ (0,1)^2`. (2) For every `F`-quasi-invariant σ-finite Borel
measure `μ` on `(0,1)`, the measured equivalence relation `(R_F, μ)` is amenable, equivalently
`μ`-hyperfinite.

*Proof of (1).* `⊆`: on each piece an element of `F` is `t ↦ 2^k t + d`, and
`d = f(b) - 2^k b` is dyadic because `b` and `f(b)` are dyadic breakpoints.
`⊇`: let `t, w ∈ (0,1)` with `w = 2^k t + d`.
- If `t` is dyadic, `w` is dyadic, and `F` is transitive on the dyadic rationals of `(0,1)`
  (a consequence of the lemma quoted below).
- If `t` is not dyadic, choose `n` so large that the standard dyadic interval
  `I = [p/2^n, (p+1)/2^n]` containing `t` satisfies `1 ≤ p` and `p + 1 ≤ 2^n - 1`, that
  `J = 2^k I + d ⊆ (0,1)` is not an end interval either, and that `2^(n-k) d ∈ Z`. Then
  `J = [q/2^(n-k), (q+1)/2^(n-k)]` with `q = p + 2^(n-k) d ∈ Z` is a standard dyadic interval.
  Partition `[0, min I]` and `[0, min J]` into standard dyadic intervals with the same number
  of pieces (halving one piece raises the count by one, so both counts can be matched), and
  likewise `[max I, 1]` and `[max J, 1]`. This gives two standard dyadic subdivisions of
  `[0,1]` with equally many pieces, with `I` and `J` at the same position. By
  Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Enseign. Math. 42
  (1996), Lemma 4.2, there is `f ∈ F` mapping each piece of the first subdivision affinely
  onto the corresponding piece of the second. On `I` it is the increasing affine map onto `J`,
  which is `t ↦ 2^k t + d`, so `f(t) = w`. ∎

*Proof of (2).* Replacing `μ` by an equivalent probability measure changes nothing. Enumerate
`Aff = {g_0 = id, g_1, ...}` and set `ν = sum_j 2^(-j) (g_j)_* μ` on `R`. It is a probability
measure and `Aff`-quasi-invariant, since `(g)_* ν` and `ν` have the same null sets. For Borel
`E ⊆ (0,1)`: `ν(E) = 0` iff `μ(g_j^(-1)(E) ∩ (0,1)) = 0` for all `j`. By (1),
`g_j^(-1)(E) ∩ (0,1)` lies in the `R_F`-saturation of `E`, which is `μ`-null when `μ(E) = 0`
by quasi-invariance under the countable group `F`. The term `j = 0` gives the converse. So
`ν|_(0,1)` is equivalent to `μ`.
- `R_Aff` is the orbit relation of a non-singular action of a countable amenable group on
  `(R, ν)`, so it is `ν`-amenable (Zimmer 1977), hence `ν`-hyperfinite (Connes–Feldman–Weiss
  1981): up to a `ν`-null saturated set it is an increasing union of finite Borel relations
  `E_n`.
- Intersecting with `(0,1)^2` gives finite relations `E_n ∩ (0,1)^2` increasing to
  `R_Aff ∩ (0,1)^2 = R_F` off a `μ`-null set. So `(R_F, μ)` is hyperfinite, hence amenable. ∎

Standard facts used, not re-read today: Zimmer, *Hyperfinite factors and amenable ergodic
actions*, Invent. Math. 41 (1977); Connes–Feldman–Weiss, *An amenable equivalence relation is
generated by a single transformation*, Ergodic Theory Dynam. Systems 1 (1981). Textbook
account: Kechris–Miller, *Topics in Orbit Equivalence*, LNM 1852 (2004).

**Consequence (Monod's mechanism is unavailable for F).** N. Monod, *Groups of piecewise
projective homeomorphisms*, arXiv:1209.5229, Theorem 1.1, proves `H(A)` non-amenable for
`A ≠ Z` by showing that its orbit relation on the projective line is non-amenable. The input
is Carrière–Ghys (Théorème 3 of Monod's reference [22]): the equivalence relation induced by
`PSL_2(A)` is non-amenable because `PSL_2(A)` contains a non-discrete non-abelian free
subgroup (read from the ar5iv render, 2026-09-13; the proof was not re-read). For `F` the
local maps form the solvable group `Aff`, and Theorem B shows that every orbit relation of `F`
on `(0,1)` is amenable for every quasi-invariant measure. So no argument of the form "some
measured orbit relation of `F` on the interval is non-amenable" can prove non-amenability of
`F`. Non-amenability of `F`, if true, is invisible to the measured orbit structure: it would
have to live in the stabilizers, which contain copies of `F`.

## 3. Proposition C: evacuation schemes for {x_0, x_1} need capacity at least 3

Guba's survey (arXiv:2305.07113v4, §2, Proposition 2.4) records that `F` is non-amenable iff
it has an *evacuation scheme*: an infinite simple path `p_v` from each vertex `v` of a Cayley
graph such that each directed edge lies on at most `C` of the paths, for some constant `C`
(the capacity).

**Proposition C.** Let `Γ` be the Cayley graph of `F` for `{x_0^(±1), x_1^(±1)}`, which is
4-regular. If a finite vertex set `A` has average induced degree `δ(A) > 4 - 1/C`, then `Γ`
has no evacuation scheme of capacity `C`. Since some finite `A` has `δ(A) > 3.5`, every
evacuation scheme for `{x_0, x_1}` has capacity at least `3`.

*Proof.* Each `p_v` with `v ∈ A` is infinite and simple, so it leaves the finite set `A` and
traverses at least one directed edge from `A` to its complement. There are exactly
`|∂A| = 4|A| - δ(A)|A|` such directed edges, each used at most `C` times, so
`|A| ≤ C(4 - δ(A))|A|`, i.e. `δ(A) ≤ 4 - 1/C`. Guba, arXiv:2210.12304 (survey Theorem 2.8),
gives finite subgraphs with density `> 3.5 = 4 - 1/2`, so capacity 2 is impossible. ∎

This corrects the "open for `C ≥ 2`" line of `thompson-f-certificate-shapes-2026-09-12.md`
for the generating set `{x_0, x_1}`: capacity 2 is dead there, and the first open capacity is
3. (For the three-element generating sets named there, the survey's bound `|∂Y| < |Y|` kills
capacity 1 only.)

## 4. Certificate classes on the non-amenable side (status after this pass)

| Class | Status |
|---|---|
| Free subgroup | dead: none exist (`thompson-f-has-no-free-subgroups`) |
| Kazhdan-type uniform gap | dead: `F ⊂ V` has the Haagerup property |
| Finitely many closed-walk counts | dead (`thompson-f-moment-data-cannot-certify-nonamenability`) |
| Rapid decay / Haagerup-inequality norm bounds | dead: `F` contains `Z ≀ Z` (`⟨x_0, g⟩` for a bump `g` supported in `(1/4,1/2)`, whose `x_0`-conjugates have disjoint supports), an amenable subgroup of exponential growth, and an amenable subgroup of a group with RD has polynomial growth (Jolissaint 1990; theorem number not re-read) |
| Ponzi scheme or non-amenable Schreier graph on an orbit of points or finite configurations of `(0,1)` | **dead, Theorem A** |
| Non-amenable measured orbit relation on `(0,1)` (Monod's mechanism) | **dead, Theorem B** |
| Evacuation scheme, capacity `≤ 2`, for `{x_0, x_1}` | **dead, Proposition C**; capacity `≥ 3` open, equivalent to the problem as `C → ∞` |
| Non-Ore pair in `K[F]` | open, equivalent; large classes excluded (`thompson-f-certificate-shapes-2026-09-12.md`) |
| Non-amenable Schreier graph `F/H` for an amenable `H` | open, equivalent for every amenable `H` (co-amenability); by Theorem A, `H` must contain no end-rigid stabilizer, which is automatic for amenable `H` unless `F` is amenable, so this adds no constraint |
| C*-simplicity of `T` (or of `F`) | open, equivalent (Le Boudec–Matte Bon arXiv:1605.01651 Theorem 1.6; Haagerup–Olesen arXiv:1609.05086 Theorem 4.5); see part 2 |

Part 2 (C*-simplicity class, Haagerup–Olesen averaging criterion) follows in a separate file.
