---
rg: 2
id: rover-nekrashevych-polynomial-activity-tower-sigma-full-proof
kind: route
title: Check the heredity hypotheses along the activity tower V_{d,r} <= V_{d,r}G_0 <= ... <= V_{d,r}G_n, relative to all finite sets of rational points
target: rover-nekrashevych-polynomial-activity-tower-sigma-full
requires:
  - germ-extension-point-fixer-sigma-heredity
  - higman-thompson-rational-point-fixers-are-f-infinity
  - rover-nekrashevych-characters-are-sum-invariant
---

Definitions are those of the claim. `Φ_m`, "localizes", and (H1)–(H4) are those of
`germ-extension-point-fixer-sigma-heredity`. Items (Stab) and (Germ) are those of
`higman-thompson-rational-point-fixers-are-f-infinity`.

Write `C = C_{d,r} = X_r × X_d^ω` and `V = V_{d,r}`. Let `P ⊂ C` be the set of rational points.

## 0. Cones and counting

- A *cone* is `C_α = αX_d^ω` with `α in X_r × X_d^*`. Two cones are nested or disjoint.
- Every nonempty clopen `E ⊆ C` is a finite disjoint union of cones.
- The number of cones mod `d−1` does not depend on the decomposition. Write it `[E] in Z/(d−1)`.
  - This is standard: splitting one cone into its `d` children adds `d−1`, and any two decompositions have a common
    refinement obtained by splitting.
  - `[C] = r` and `[C_α] = 1`.
- Two nonempty clopen sets `E` and `E'` with `[E] = [E']` are related by a *prefix replacement*: decompose both, split
  cones until the numbers agree, then map `γ_jψ ↦ γ'_jψ`.

For a self-similar `H`, a map `f: E -> E'` between clopen sets is *`H`-piecewise* if there are a cone decomposition
`E = ⊔ C_{α_j}` and `h_j in H` with `f(α_jψ) = β_j h_j(ψ)`, where the cones `C_{β_j}` decompose `E'`. By definition,
`V_{d,r}H` is the set of `H`-piecewise homeomorphisms `C -> C`.

## 1. Lemma P (patching)

**Statement.** Let `H` be self-similar and `E, E' ⊆ C` clopen, with nonempty complements and `[E] = [E']`. Let
`f: E -> E'` be an `H`-piecewise homeomorphism, and let `M ⊂ C ∖ (E ∪ E')` be finite. Then some `f' in V_{d,r}H`
agrees with `f` on `E` and is the identity on a neighbourhood of `M`. Off `E`, `f'` is a prefix replacement.

**Proof.**

1. Choose a clopen neighbourhood `N` of `M` inside `C ∖ (E ∪ E')`, small enough that `U = C ∖ (E ∪ N)` and
   `U' = C ∖ (E' ∪ N)` are nonempty. This is possible because `C ∖ E` and `C ∖ E'` are nonempty open sets without
   isolated points.
2. `[U] = r − [E] − [N] = r − [E'] − [N] = [U']`.
3. Let `f'` be `f` on `E`, the identity on `N`, and a prefix replacement `U -> U'`. ∎

## 2. Lemma L (localization)

**Statement.** Let `H` be self-similar and `Γ_H = V_{d,r}H`. Every nonzero `χ in Hom(Γ_H,R)` is nonzero on
`Fix_{Γ_H}(M)` for every finite `M ⊂ C`. So `Γ_H` localizes over every subset of `C`.

**Proof.**

1. **`χ(V) = 0`.** `V_{d,r}` has finite abelianization (Higman 1974, at statement level). For `r = 1` this is also
   `rover-nekrashevych-characters-are-sum-invariant`.
2. **Cone copies.** For `h in H` and a proper cone `C_u`, let `h_(u)` be `uψ ↦ uh(ψ)` on `C_u` and the identity
   elsewhere. Then `h_(u) in Γ_H`.
   - For proper cones `C_u` and `C_{u'}`, Lemma P (with `H = 1` and `M = ∅`) gives `v in V` with `v(uψ) = u'ψ`.
   - Then `v h_(u) v^{-1} = h_(u')`, so `χ(h_(u)) = χ(h_(u')) =: φ(h)`.
3. **Generation.** Let `f in Γ_H` with `f(α_jψ) = β_j g_j(ψ)`. Splitting once, we may assume that every `C_{α_j}` is
   proper. Let `v in V` be `α_jψ ↦ β_jψ`. Then `f = v ∘ Π_j (g_j)_(α_j)`, a product of commuting elements with
   disjoint supports. So `Γ_H = ⟨V, h_(u)⟩`, and `χ(f) = Σ_j φ(g_j)`.
4. **Conclusion.** If `χ != 0`, then `φ(h) != 0` for some `h`. Given finite `M`, pick a proper cone `C_u` disjoint
   from `M`. Then `h_(u) in Fix_{Γ_H}(M)` and `χ(h_(u)) = φ(h) != 0`. ∎

## 3. The tower

**(S1) Each `G_i` is a self-similar subgroup, for `−1 <= i <= n`.**

- `(gh)|_v = g|_{h(v)} h|_v` and `h` permutes `X_d^k`, so `θ_k(gh) <= θ_k(g) + θ_k(h)`.
- `g^{-1}|_v = (g|_{g^{-1}(v)})^{-1}`, so `θ_k(g^{-1}) = θ_k(g)`.
- `θ_k(g|_w) <= θ_{k+|w|}(g)`, and `O((k+|w|)^i) = O(k^i)`.

So each `G_i` is a subgroup closed under sections, and `G_n = G`.

**The groups.** Put `Γ_i = V_{d,r}G_i`.

- A finitary element acts on each cone of a deep enough level by a prefix replacement. So `Γ_{−1} = V`.
- `Γ_n = Γ`.

**(S2) Singular points.** Fix `−1 <= i < n`. Let `f in Γ_{i+1}` with `f(α_jψ) = β_j g_j(ψ)`, where
`g_j in G_{i+1}`. For `g in G_{i+1}` put

> `sing_i(g) = {ψ in X_d^ω : g|_w ∉ G_i for every finite prefix w of ψ}`.

**Claim.** The singular set of `f` relative to `Γ_i` is `sing(f) = ⊔_j α_j sing_i(g_j)`.

**Proof.** Let `x = α_jψ`.

1. **A good prefix makes `x` nonsingular.** Suppose `w` is a prefix of `ψ` with `g_j|_w in G_i`. Lengthen `w` so that
   `C_{α_jw}` and its image are proper. On `C_{α_jw}`, `f` is `α_jwψ' ↦ β_j g_j(w) g_j|_w(ψ')`, which is
   `G_i`-piecewise. Lemma P (with `M = ∅`) extends it to an element of `Γ_i`.
2. **A nonsingular `x` has a good prefix.** Suppose `f` agrees with `f_0 in Γ_i` on a neighbourhood of `x`.
   - For a long prefix `w` of `ψ`, both are given by single pieces on `C_{α_jw}`:
     `β_j g_j(w) g_j|_w(ψ') = γ h(ψ')` for all `ψ'`, with `h in G_i` by (S1).
   - Suppose `|γ| < |β_j g_j(w)|`. The letter in position `|γ|+1` of the right side takes every value as `ψ'` varies,
     because `h` is onto. On the left side that letter is fixed. This is impossible, and the case `|γ| > |β_j g_j(w)|`
     is symmetric.
   - So `γ = β_j g_j(w)` and `g_j|_w = h in G_i`. ∎

(S1) also shows that once a section lies in `G_i`, every deeper section along the same path does too.

## 4. The circuit lemma

Fix `−1 <= i < n` and `g in G_{i+1}`. Let `Q = {g|_v : v in X_d^*}`, which is finite because `G` is contracting. The
*automaton* of `g` has vertex set `Q` and a labelled edge `q -x-> q|_x` for each `x in X_d`. A walk labelled `u` from
`q` ends at `q|_u`.

**(a) Closed walks at a nontrivial state are powers of one word.**

- Let `q != 1` in `Q`, and let `u` and `v` be labels of closed walks at `q`, with `uv != vu`.
- Put `a = u^{|v|}` and `b = v^{|u|}`. These have the same length `ℓ`, and `a != b`: by Lyndon–Schützenberger,
  `a = b` would make `u` and `v` powers of a common word, so they would commute.
- The `2^j` words in `{a,b}^j` are distinct and all satisfy `q|_w = q != 1`. So `θ_{jℓ}(q) >= 2^j`.
- `q = g|_{v_0}` for some `v_0`, so `θ_{jℓ+|v_0|}(g) >= θ_{jℓ}(q)`. This contradicts polynomial growth.

So any two closed-walk labels at a nontrivial `q` commute, and hence are powers of one primitive word.

**Consequence.** Consider the automaton restricted to `Q ∖ {1}`. Take a strongly connected component of it that
contains an edge. Each of its states has exactly one outgoing edge inside the component: two such edges with letters
`x != y` would close up to closed walks beginning with different letters, which are not powers of one word. So the
component is a simple cycle. Call it a *circuit*. From a state `q` on it, the *lap label* `λ_q` is the label once
around. Then `q|_{λ_q} = q`, and every closed walk at `q` has label a power of `λ_q`.

**(b) No descent from a circuit into a circuit outside `G_i`.**

**Statement.** Let `A'` and `A` be distinct circuits. Suppose a walk leaves `A'` at a state `q'` and reaches a state
`q in A` with `q ∉ G_i`. Then `θ(q') != O(k^{i+1})`. Since `q'` is a section of `g`, this contradicts `g in G_{i+1}`,
so no such configuration exists.

**Proof.**

1. **Setup.** Write the walk as `u` (length `c`), with first letter `u_1 != (λ_{q'})_1`. Put `a = |λ_{q'}|` and
   `b = |λ_q|`.
2. **Monotonicity along the lap.** The words `λ_q^t v` show `θ_{m+tb}(q) >= θ_m(q)`.
3. **Distinct words.** Fix `L`, `m_0` and `k = c + m_0 + Lab`. For `0 <= s <= L`, consider the words
   `λ_{q'}^{sb} u v`, where `v` has length `m_0 + (L−s)ab` and `q|_v != 1`.
   - They all have length `k`, and `q'|_{λ_{q'}^{sb}uv} = q|_v != 1`.
   - They are pairwise distinct. For `s < s'`, position `sab+1` holds `u_1` in the first word and `(λ_{q'})_1` in the
     second.
   - Hence `θ_k(q') >= Σ_{s=0}^{L} θ_{m_0+(L−s)ab}(q) >= (L+1) θ_{m_0}(q)`, using step 2.
4. **Case `i >= 0`.**
   - `q ∉ G_i`, so for every `K` there are infinitely many `m_0` with `θ_{m_0}(q) >= K m_0^i`.
   - Take `L = m_0 >= c`. Then `k <= (2+ab) m_0` and `θ_k(q') >= K m_0^{i+1} >= K k^{i+1} / (2+ab)^{i+1}`.
   - `K` is arbitrary, so `θ(q') != O(k^{i+1})`.
5. **Case `i = −1`.**
   - `q` is not finitary, so some `m_0` has `θ_{m_0}(q) >= 1`.
   - Then `θ_k(q') >= L+1` for arbitrarily large `L`, so `θ(q')` is unbounded. ∎

**(c) Singular paths.**

**Statement.** `sing_i(g)` is finite. Each of its elements has the form `wλ_q^∞`, where `q = g|_w` is a state on a
circuit, `q ∉ G_i` and `q in N`.

**Proof.**

1. Let `ψ in sing_i(g)` and let `q_k = g|_{ψ_1...ψ_k}`. By (S1) every `q_k` lies in `D = Q ∖ G_i`, and `1 ∉ D`.
2. **The walk ends in a circuit.** The walk eventually stays in one strongly connected component of the automaton on
   `D`. That component contains an edge, so it lies in a circuit `A`. The walk then follows the unique edges of `A`, so
   it runs around all of `A`, and `A ⊆ D`.
3. **Before the circuit.** Before entering `A` for the last time, the walk visits no state on any other circuit `A'`,
   by (b). It does not leave `A` and return either, since that excursion would lie in the component of `A`. So the
   earlier states lie on no circuit. None of them repeats, because a repeat would put it on a closed walk.
4. **The form of `ψ`.** `ψ = wλ_q^∞` with `|w| < |Q|` and `q = g|_w in A`. So `|sing_i(g)| <= Σ_{ℓ<|Q|} d^ℓ`.
5. **`q in N`.** `q = g|_{wλ_q^t}` for every `t`, and `|wλ_q^t| -> ∞`, so `q in N`. ∎

**(d) Tails.** Let `R` be the finite set of sequences `λ_q^∞`, where `q in N ∖ {1}` and `q` lies on a circuit of its
own automaton. By (a), `λ_q` depends only on `q`. Put `O_R = {γρ : γ in X_r × X_d^*, ρ in R}`. It is a finite union
of `V`-orbits of rational points: points with the same tail `ρ` are exchanged by prefix replacements, using Lemma P.

By (S2) and (c), for every `i` the singular points of `Γ_{i+1}` relative to `Γ_i` are finite for each element and lie
in `O_R ⊆ P`.

## 5. Lemma G (germ index at rational points)

**Statement.** Let `H <= G` be self-similar and `p = αβ^∞` rational, with `β` primitive. Then
`|(V_{d,r}H)_p : (V)_p| <= |β|·|N|`.

**Proof.**

1. **Representatives.** Let `f in V_{d,r}H` fix `p`. For all large `k`, `f(αβ^kψ) = γ_k h_k(ψ)`.
   - Here `h_k` is a section of some `g_j` at depth `>= L(g_j)`, so `h_k in N`.
   - Also `|γ_k| >= |α|`.
   - `f(p) = p` makes `γ_k` a prefix of `αβ^∞`. Write `|γ_k| = |α| + a_k|β| + j` with `0 <= j < |β|`.
   - Passing from `k` to `k+1` replaces `γ_k` by `γ_k h_k(β)`, which is longer by `|β|`, and `h_k` by `h_k|_β`. So `j`
     does not depend on `k`.
2. **Pigeonhole.** Take more than `|β||N|` germs at `p`, and represent them at one common `k`. Two of them, from `f`
   and `f'`, share `(j, h_k)`.
3. **Same coset.** Write `π = αβ^{a}β_{<=j}` and `π' = αβ^{a'}β_{<=j}`. On `C_π`,
   `f'∘f^{-1}(πχ) = f'(αβ^k h_k^{-1}(χ)) = π'χ`. This is a prefix replacement, so its germ at `p` lies in `(V)_p`, by
   Lemma P. So the two germs lie in one coset of `(V)_p`. ∎

## 6. The hypotheses relative to a finite set of rational points

Fix `−1 <= i < n` and a finite `M ⊂ P`. Put `B = Γ_i`, `E = Γ_{i+1}`, `B_M = Fix_B(M)` and `E_M = Fix_E(M)`.

**(R0) Agreeing with the base near a point.** Let `f in E_M` and `x in C`. If `f` agrees with some element of `B` near
`x`, then it agrees with some element of `B_M` near `x`.

**Proof.**

1. Take a proper cone `C_0 ∋ x` on which `f` is a single `G_i`-piece, with `C_0 ∩ M ⊆ {x}` and `f(C_0)` a proper cone.
2. Put `M' = M ∖ {x}`. Then `f(C_0) ∩ M' = f(C_0 ∩ M') = ∅`, because `f` fixes `M'` pointwise.
3. Lemma P, applied to `f|_{C_0}` and `M'`, gives `f' in B` equal to `f` on `C_0` and the identity near `M'`.
4. If `x in M`, then `f'(x) = f(x) = x`. So `f' in B_M`. ∎

The converse is trivial. So for `f in E_M` the singular set relative to `B_M` equals the singular set relative to `B`.

**(H1) `E_M` is a finite germ extension of `B_M`, with `sing(E_M) ⊆ O_R ⊆ P`.**

- The singular sets are those of section 4, by (R0). They are finite and lie in `O_R`.
- **Condition 2.** Let `f in E_M` have no singular points.
  1. By (S2), every point `α_jψ` has a prefix `w` of `ψ` with `g_j|_w in G_i`.
  2. Finitely many such cones `C_{α_jw}` cover `C`. The maximal ones partition it, and `f` is a `G_i`-piece on each.
  3. The images are cones and partition `C`. So `f in B ∩ E_M = B_M`.

  Conversely, elements of `B_M` have no singular points.
- **Condition 3.** Let `f in E_M` and `p in sing(f)`.
  1. Take a proper cone `C_0 ∋ p` on which `f` is a single `G_{i+1}`-piece, with
     `C_0 ∩ (sing(f) ∪ M) ⊆ {p}` and `f(C_0)` a proper cone.
  2. Lemma P, applied with `M' = M ∖ {p}` and `H = G_{i+1}`, gives `f' in E` with `f' = f` on `C_0`, the identity near
     `M'`, and a prefix replacement elsewhere. Then `f'` fixes `M`.
  3. Off `C_0`, `f'` is locally in `V`. On `C_0 ∖ {p}` it agrees locally with `f`, which is nonsingular there. So
     `sing(f') = {p}`.

**(H3) Finite germ index.** Let `p in sing(E_M)`, so `p` is rational. Write `p = αβ^∞` with `β` primitive.

1. **The shift lies in `B_M`.** Take `k` large, so that `C_{αβ^k} ∩ M ⊆ {p}`. Lemma P extends the prefix replacement
   `C_{αβ^k} -> C_{αβ^{k+1}}` to some `t' in Fix_V(M)`.
2. **It generates `(V)_p`.** By (Germ) with `S = {p}`, the germ `(t')_p` generates `(V)_p`, which is infinite cyclic.
3. **The index bound.** All germ groups here are subgroups of the group of germs at `p` of `Homeo(C)`, and
   `(V)_p <= (B_M)_p <= (E_M)_p <= (E)_p`. Lemma G with `H = G_{i+1}` gives
   `|(E_M)_p : (B_M)_p| <= |(E)_p : (V)_p| < ∞`.

**(H2) Finitely many orbits.** Let `Z` be the finite set consisting of `R` and the tails `β^∞` of the points of `M`.
Let `O'` be the set of all `γz` with `z in Z`. Then `O' ⊇ O_R ∪ M`.

**Claim.** `V` has finitely many orbits on `O'^N` for every `N`.

**Proof.**

1. Fix the pattern of equal entries; there are finitely many patterns. Let `x_1,...,x_s` be the distinct entries, with
   `x_l = γ_l z_l` and `z_l in Z`.
2. Every `z in Z` is periodic, `z = ρz`. So each `γ_l` can be lengthened freely. Lengthen them until the cones
   `C_{γ_l}` are pairwise disjoint, then once more so that their union is not all of `C`.
3. Two tuples with the same pattern and the same `(z_1,...,z_s)` are related by the prefix replacement
   `γ_lψ ↦ γ'_lψ`. Lemma P extends this to some `v in V`, since `[∪C_{γ_l}] = s = [∪C_{γ'_l}]`.
4. So there are at most `Σ_patterns |Z|^s` orbits. ∎

**Consequence.** Let `M` be listed in order. The map from `Fix_V(M)`-orbits of `y in O_R^{m+1}` to `V`-orbits of
`(M,y)` is injective. So `Fix_V(M)`, and hence `B_M ⊇ Fix_V(M)`, has finitely many orbits on `sing(E_M)^{m+1}`.

**(H4) Orbits.** Let `p in sing(E_M)`.

- **`p in M`.** `E_M` fixes `p`. So `{p}` is a single `B_M`-orbit and the whole `E_M`-orbit.
- **`p ∉ M`.**
  1. Take a proper cone `C_0 ∋ p` disjoint from `M`.
  2. The complement of `C_0` and of a small neighbourhood of `M` contains infinitely many pairwise disjoint cones
     `C_1, C_2, ...`.
  3. Lemma P extends the prefix replacement `C_0 -> C_l` to some `v_l in Fix_V(M)`. The points `v_l(p) in C_l` are
     distinct, so `B_M·p` is infinite.

**Localization.** `B` and `E` localize over `P`, by Lemma L.

## 7. Conclusion

**The base.** `Φ_m(Γ_{−1}, P) = Φ_m(V, P)` holds for every `m`.

- `Fix_V(M)` has type `F_∞` for every finite `M ⊂ P`, by (Stab).
- `Hom(V,R) = 0`, so the condition on characters is vacuous.

**The steps.** For each `−1 <= i < n` and every `m`, the pair `Γ_i <= Γ_{i+1}` satisfies the hypotheses of
`germ-extension-point-fixer-sigma-heredity`, by section 6.

**The tower.** Its tower corollary, applied to `Γ_{−1} <= Γ_0 <= ... <= Γ_n = Γ`, gives:

- `Γ` has type `F_∞`;
- `Σ^∞(Γ) = S(Γ)`;
- every `N ⊴ Γ` with `Γ/N` abelian has type `F_∞`. ∎

## Calibration

- **Bounded `G` (`n = 0`).** The tower is `V <= V_{d,r}G`. The route then reproves
  `rover-nekrashevych-bounded-automata-sigma-invariants-full`, with the relative statement at all finite sets of
  rational points. The circuit lemma reduces to the fact that a bounded automaton has disjoint circuits and no chain of
  two. Its singular points are the points `wλ^∞`, as in Belk–Hyde–Matucci `prop:BoundedAutomataGermExtension`.
- **Where contraction is used.**
  - Finiteness of `Q`, and of the tail set `R`, in section 4(d).
  - Lemma G.

  Without contraction, a circuit state `q` with `q(λ_q) = λ_q` gives infinitely many distinct sections `q^j|_{λ_q} = q^j`.
  For example, take `b = (b,a)` over the odometer `a`: then `b^j` is a section of itself for every `j`. So the nucleus
  argument has no replacement there.
- **Exponential activity.** Section 4(a) fails. For example, for `q = (q,q)σ` every word is a closed-walk label.
