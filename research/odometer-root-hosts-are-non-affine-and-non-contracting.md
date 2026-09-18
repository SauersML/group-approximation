---
rg: 2
id: odometer-root-hosts-are-non-affine-and-non-contracting
kind: claim
title: On the m-ary tree the l-th roots of the odometer are exactly the rational translations by 1/l, and the translation copy of Z_(S) has only affine normalizer; so a finitely generated self-similar group containing the odometer and its roots at infinitely many primes is not contracting, not of polynomial activity, and does not normalize its translations
requires:
  - fg-linear-groups-have-roots-at-finitely-many-primes
distinct_from:
  aff-n-z-localized-lies-in-fp-self-similar-group: that OPEN node asks for a finitely presented self-similar overgroup of Aff_n(Z_(l)) and notes it cannot be affine; this proves the non-affine part intrinsically (every normalizer of the translations is affine) and adds that such a host cannot be contracting or of polynomial activity, the two standard sources of self-similar finiteness theorems.
  fg-linear-groups-embed-in-fp-self-similar-groups: that embeds every finitely generated linear group in a finitely presented self-similar group R^N ⋊ E_N(R) over a finitely generated commutative ring; those hosts are linear, so they contain no Z_(S) and reach none of the groups considered here.
  z-semilocalized-embeds-in-fp-rf-group: that is the target (SL); this rules out the contracting and polynomial-activity self-similar witnesses of the translation type.
---

**ESTABLISHED** (lane bh-gln-tracka, 2026-09-18; elementary, lane proof, not reviewed; no priority claimed. The
root and centralizer facts for the odometer are folklore.)

## Setting

- `m >= 2`, and `S` is the set of primes dividing `m`.
- `X* ` is the `m`-ary rooted tree, with boundary `X^ω ≅ Z_m = ∏_(p∈S) Z_p` (least significant digit first).
- For `z ∈ Z_m` and `u ∈ Z_m^×`, `τ_z(x) = x + z` and `μ_u(x) = u x` are tree automorphisms. They preserve every
  congruence modulo `m^k`. `a = τ_1` is the odometer.
- `T = {τ_c : c ∈ Z_(S)} ≅ Z_(S)`.

## Theorem

1. **Sections.** For `c ∈ Z_m` and a word `w` of length `k`, representing the integer `[w]`, let
   `r = ([w] + c) mod m^k`. Then `τ_c` maps `w` to the word representing `r`, and its section at `w` is `τ_(c_w)`
   with `c_w = ([w] + c − r) / m^k`.
   - If `c` is rational then `c_w` is rational, so `τ_c` is finite-state, and `T` is a self-similar group
     (closed under sections).
   - If `c = M/ℓ` with `ℓ ∉ S` prime and `ℓ ∤ M`, every `c_w` has exact denominator `ℓ` and real absolute value
     less than 2. In particular every section of `τ_c` is nontrivial.
2. **Roots and centralizer.**
   - The centralizer of `a` in `Aut(X*)` is `{τ_z : z ∈ Z_m}`.
   - For a prime `ℓ ∉ S`, the only `ℓ`-th root of `a` in `Aut(X*)` is `τ_(1/ℓ)`.
   - For a prime `q ∈ S`, `a` has no `q`-th root in `Aut(X*)`.
3. **Normalizer.** Let `Z ⊆ A ⊆ Z_(S)` be a subgroup. The normalizer of `{τ_c : c ∈ A}` in `Aut(X*)` consists of
   the affine maps `x ↦ u x + z` with `z ∈ Z_m` and `u ∈ Q^×` such that `uA = A`.
4. **Hosts.** Let `G ≤ Aut(X*)` be finitely generated, contain `a`, and contain an `ℓ`-th root of `a` for infinitely
   many primes `ℓ`. Then:
   - **(a)** `τ_(1/ℓ) ∈ G` for each such `ℓ`;
   - **(b)** `G` contains non-affine elements, and `G ∩ T` is not normal in `G`;
   - **(c)** if `G` is self-similar, it is not contracting;
   - **(d)** `G` is not contained in Sidki's group `Pol(∞)` of automorphisms of polynomial activity.
5. **Linear hosts.** The hosts `R^N ⋊ E_N(R)` of `fg-linear-groups-embed-in-fp-self-similar-groups` lie in
   `GL_(N+1)(R)`, so they are finitely generated linear groups. By
   `fg-linear-groups-have-roots-at-finitely-many-primes` they contain no `Z_(S)`, and no element with roots at
   infinitely many primes.

## Proof

**1.** Write `x = [w] + m^k x'`. Then `x + c = r + m^k (x' + c_w)`, which gives the image of `w` and the section.
- For rational `c`, `c_w` ranges over rationals of bounded height with the denominator of `c`, a finite set. So
  `τ_c` has finitely many states. The section of `τ_c ∈ T` is again in `T`, since `c_w ∈ Z_(S)`: it is rational with
  denominator prime to `m`, and lies in `Z_m`.
- For `c = M/ℓ`: `m^k c_w = [w] − r + M/ℓ`, so `c_w = (Nℓ + M)/(ℓ m^k)` for an integer `N`, with `ℓ ∤ Nℓ + M`.
  Since `c_w ∈ Z_m`, `m^k` divides `Nℓ + M`, and `c_w = M'/ℓ` with `ℓ ∤ M'`. Its real value is
  `([w] − r)/m^k + M/(ℓ m^k)`, where the first term lies in `(−1, 1)`. The bound `|c_w| < 2` holds for `|M| < ℓ`,
  and for larger `|M|` at every level `k` with `m^k > |M|/ℓ`.

**2.** On level `k`, `a` acts as a single `m^k`-cycle, and in `Sym(m^k)` the centralizer of a full cycle is the cyclic
group it generates. So an `x` commuting with `a` acts on level `k` as `a^(j_k)`, with `j_(k+1) ≡ j_k mod m^k` by
compatibility. Then `x = τ_z` with `z = lim j_k`.

An `ℓ`-th root `h` of `a` commutes with `a`, so `h = τ_z` with `ℓ z = 1` in `Z_m`. That has the unique solution
`z = 1/ℓ` when `ℓ ∉ S`, and no solution when `ℓ ∈ S`.

**3.** Let `x` normalize `T_A = {τ_c : c ∈ A}`.
- `A ⊇ Z` is dense in `Z_m`, so `x` also normalizes the closure `{τ_z : z ∈ Z_m}`.
- Conjugation by `x` restricts to an automorphism of `A ≅` a subgroup of `Q`, which is multiplication by some
  `u ∈ Q^×` with `uA = A`.
- By continuity, `x τ_z x^(-1) = τ_(uz)` for every `z ∈ Z_m`. Also `μ_u τ_z μ_u^(-1) = τ_(uz)`, where `u ∈ Z_m^×`
  because `uA = A` forces the numerator and denominator of `u` to be prime to `m`.
- So `μ_u^(-1) x` centralizes `a`, and by 2 it equals `τ_z` for some `z`. Hence `x = μ_u τ_z`, which is affine.

Conversely, each such map normalizes `T_A`.

**4(a)** is part 2.

**4(b).** Suppose every element of `G` were affine, `x ↦ u x + z` with `u ∈ Z_m^×` and `z ∈ Z_m`.
- Then `G` embeds in `∏_(p∈S) (Q_p ⋊ Q_p^×) ≤ ∏_(p∈S) GL_2(Q_p)`.
- Each `Q_p` embeds in `C`, so this finitely generated `G` embeds in `GL_(2|S|)(C)` and is linear.
- But `a ∈ G` has roots at infinitely many primes, contradicting
  `fg-linear-groups-have-roots-at-finitely-many-primes`.

If `G ∩ T` were normal in `G`, then 3 with `A = G ∩ T ⊇ Z` would make `G` affine. So it is not normal.

**4(c).** Let `N` be a finite nucleus: every element has all its sections in `N` from some level on.
- By 1, all sections of `τ_(1/ℓ)` at every level are translations by rationals of exact denominator `ℓ`.
- So `N` contains, for each of the infinitely many `ℓ` in 4, an element `τ_c` with `c` of exact denominator `ℓ`.
- These elements are pairwise distinct, so `N` is infinite, a contradiction.

**4(d).** By 1, `τ_(1/ℓ)` has a nontrivial section at every one of the `m^k` vertices of level `k`. So its activity
grows exponentially, and `τ_(1/ℓ) ∉ Pol(∞)`. ∎

## What this says about (SL) and 5.3(5)

- **The linear embedding theorem does not reach divisible inputs.** Part 5 answers the check asked of
  `fg-linear-groups-embed-in-fp-self-similar-groups`. Its finite presentation comes from elementary groups over
  finitely generated commutative rings (`elementary-groups-over-polynomial-s-integers-are-fp`). Such a ring inverts only finitely
  many primes (generic freeness), so the method cannot see `Z_(S)`.
- **The natural self-similar model of `Z_(S)`, the `m`-adic translations, is maximally expensive.**
  - Its elements have exponential activity and unboundedly many states.
  - Any finitely generated host must be non-affine and must not normalize the translations.
  - It cannot be contracting, and it cannot lie in `Pol(∞)`.
- **What that costs for finite presentation.** The finite-presentation results for self-similar groups that this lane
  found on main use linearity (part 5) or contraction (e.g. `contracting-srn-rational-stabilizers-are-fp`). Both are
  excluded here.
  A finitely presented self-similar witness of this translation type needs a new finite-presentation mechanism.
- **Scope.** Parts 4(a)–(d) assume the odometer is in `G`. A copy of `Z_(S)` in `Aut(X*)` whose generator acts
  level-transitively is conjugate in `Aut(X*)` to `T`, since level-transitive automorphisms of a regular rooted
  tree are conjugate to the odometer (folklore, recalled). But the conjugator need not be finite-state, so (c) and
  (d) are not claimed for such copies.

## Lesson for general BH

Divisibility in a rooted tree is carried by the odometer's own centralizer: the roots of `a` are forced to be `m`-adic
translations. Those are finite-state but exponentially active, with state sets that grow with the prime. So a
self-similar group that takes roots of `a` at infinitely many primes forgoes both standard finiteness engines,
linearity (rings) and contraction (nucleus).

This is the tree-automaton form of the carrier principle: the input's arithmetic (all primes) cannot be compressed
into finitely many states. It has to be carried either by a ring, which pays in `K_2`, or by a non-contracting,
non-linear automaton group, for which no finiteness theorem is known.
