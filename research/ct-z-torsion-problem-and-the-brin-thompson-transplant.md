---
rg: 2
id: ct-z-torsion-problem-and-the-brin-thompson-transplant
kind: claim
title: "The torsion problem of CT(Z) is open: Belk–Bleak's proof for 2V (read at source) needs independent prefix replacements on two coordinates, which CT(Z) cannot supply since one slope acts on every p-adic coordinate; the rational transfer maps that do exist have alphabets of coprime sizes; in CT(Z) finite order equals tameness, and torsion is undecidable as soon as some finitely generated subgroup (for instance 2V, if it embeds) has unsolvable torsion problem; and the analog of Belk–Bleak Theorem 6.6 (reaching a residue class) is undecidable in CT_{3,5,7,11,13}(Z)"
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `ct-z-residue-partition-certificates-live-on-s-adic-coordinates`, `ct-z-finite-cycle-problems-are-undecidable`, `ct-z-conjugacy-problem-is-undecidable`.

**Status.**
- **Theorems 1–4:** lane proof, not reviewed. Theorem 4 is due to lane bh-free-58. Theorem 3 is conditional on input (H) of
  `ct-z-conjugacy-problem-is-undecidable` (Morita). No priority is claimed.
- **Open.** Whether it is decidable if a given `g ∈ CT(Z)` has finite order. This is gap (G1) of
  `ct-z-residue-partition-certificates-live-on-s-adic-coordinates`, which a route to undecidability
  of Kourovka 21.74(a) needs.
- **Printed status.** Not a printed question as far as we found: Kourovka 18.48 asks about orders
  of products of two class transpositions, which is a different question.

## Source: Belk–Bleak, read at source

J. Belk and C. Bleak, *Some undecidability results for asynchronous transducers and the
Brin–Thompson group 2V*, arXiv:1405.0982v1; Trans. AMS 369 (2017) 3157–3172.
- **Thm 1.1.** For `n ≥ 2`, `nV` has unsolvable torsion problem. It suffices to treat `2V`.
- **Thm 2.4, quoting Kari–Ollinger (MFCS 2008).** "It is undecidable whether a given complete,
  reversible Turing machine is uniformly periodic." The model is the moving-tape one, with move and
  write instructions.
- **Coding (§4).** `Φ(s_i, τ) = (σ_i ε(τ_L), ε(τ_R)) ∈ C²`. Here `σ_i` and the `α_k` are dyadic
  subdivisions, and `ε` concatenates the codes of the symbols.
  - **Thm 4.2.** `f_T = Φ∘F∘Φ^{-1} ∈ 2V`. A left move maps `R(σ_iα_k, −)` to `R(σ_j, α_k)`, a
    right move maps `R(σ_i, α_k)` to `R(σ_jα_k, −)`, and a write maps `R(σ_i, α_k)` to `R(σ_j, α_ℓ)`.
  - **Prop 4.4.** `f_T` has finite order iff `T` is uniformly periodic.
  - **Thm 4.5.** The largest order of a torsion element with at most `n` rectangles is not
    computably bounded.
- **§6.**
  - Thm 6.6: whether the orbit of a dyadic point enters a dyadic rectangle is undecidable.
  - Thm 6.7: convergence of an orbit to a given point is undecidable.
  - Thm 6.8: some `f ∈ 2V` has an attracting dyadic fixed point whose basin meets the dyadic points
    in a non-computable set.
- **The load-bearing feature.** Every step changes one coordinate by a prefix and leaves the other
  unchanged. The two half-tapes are *independent* coordinates.

## Statement

**Theorem 1 (torsion through subgroups).**
- **Reduction.** Suppose some finitely generated `H ≤ CT(Z)` has unsolvable torsion problem. Then
  the torsion problem of `CT(Z)` is unsolvable, for elements given as words in class transpositions
  or as rcwa tables. The natural targets are the finitely presented `CT_P(Z)`, `P` finite.
- **Contrapositive.** If `CT(Z)` has decidable torsion problem, then no finitely generated group
  with unsolvable torsion problem embeds in `CT(Z)`. That covers `2V`, and the finitely presented
  groups of Arzhantseva–Lafont–Minasyan with solvable word problem and unsolvable torsion problem.

**Theorem 2 (why the Belk–Bleak coding does not transplant).** Let `q = a/b` in lowest terms,
`a, b ≥ 1`, and let `R_a = ∏_{p|a} Z_p` and `R_b = ∏_{p|b} Z_p`.
1. **No independent prefix replacement.** A piece of an element of `RCWA(Z)` is one affine map
   `x ↦ qx + c`, applied to every `p`-adic coordinate at once. So no element acts on a box as a
   prefix replacement in one coordinate and as the identity in another.
2. **Rational bases.**
   - Let `D_a ⊂ R_a` be a complete residue system of `R_a/aR_a`. Every `x ∈ R_a` has a unique
     convergent expansion `x = Σ_{k≥0} d_k q^k` with `d_k ∈ D_a`.
   - The same holds on `R_b` with base `q^{-1}` and `|D_b| = b` digits.
   - Both codings are homeomorphisms from the digit spaces.
3. **Transfer.**
   - For an integer `u`, the canonical map `x ↦ (ax − u)/b`, from the class `{x : ax ≡ u (mod b)}`
     onto a class mod `a`, does two things at once. It pops the digit `u/a` from the base-`q^{-1}`
     tape on `R_b`, and pushes the digit `−u/b` onto the base-`q` tape on `R_a`.
   - A bijective, symbol-preserving transfer of one alphabet between the two tapes would need
     `a = b`, which is impossible for `q ≠ 1`.
4. **Writes.** A piece with slope `1` is a translation `x ↦ x + c` with `c ∈ Z`. It changes the
   digits of both tapes at once, with carries that can reach arbitrarily deep.

So the natural transplant gives *rational-base two-stack machines*: half-tapes over alphabets of
coprime sizes `a` and `b`, with writes that carry. Kari–Ollinger's theorem is about standard
reversible Turing machines, and no undecidability result for uniform periodicity of this model is
known here.

**Theorem 3 (the Belk–Bleak Theorem 6.6 analog in CT(Z)).** It is undecidable, given
`g ∈ CT_{3,5,7,11,13}(Z)`, `n ∈ Z` and a residue class `C`, whether the forward `g`-orbit of `n`
meets `C`. This is conditional on (H).

**Theorem 4 (tame = finite order in CT(Z); communicated by lane bh-free-58).** An element of
`CT(Z)` is tame in Kohl's sense (it permutes a finite partition into classes and is affine on each
part) iff it has finite order. So the torsion problem of `CT(Z)` is exactly the decidability of
tameness, the question behind Kohl's `IsTame`. An infinite-order YES instance of 21.74(a) must have
a part that meets at least two affine pieces.

## Proofs

**Theorem 1.** Fix words in class transpositions for the generators of `H`. Substituting them
turns a word over `H` into a word in class transpositions whose rcwa table is computable, and the
element keeps its order. ∎

**Theorem 2.**
1. A piece `r(m) → s(n)` extends to `Ẑ` as `x ↦ s + (n/m)(x − r)` in every coordinate.
   The identity in `Z_3`, say, forces `n = m` and `s = r`, and then the map is the identity in
   `Z_2` as well.
2. `b` is a unit of `R_a`, so `qR_a = aR_a` and `R_a/aR_a ≅ Z/a`. Iterating `x = d_0 + qx_1` gives a
   remainder `q^K x_K ∈ a^K R_a → 0`. Uniqueness and bicontinuity are digit by digit. The same
   argument works on `R_b` with `q^{-1}R_b = bR_b`.
3. `a` is invertible mod `b`, so `{x : ax ≡ u (mod b)}` is a class mod `b`, and on it
   `(ax − u)/b ∈ Z`.
   - **On `R_b`.** The condition says `x_b ≡ u/a (mod bR_b)`, i.e. the top digit is `u/a`. Then
     `(ax_b − u)/b = q(x_b − u/a)`, which is the rest of the tape.
   - **On `R_a`.** `(ax_a − u)/b = −u/b + qx_a`, which is the tape with `−u/b` pushed on top.
   - **Alphabet sizes.** A bijective coding of the `R_b` tape uses `b` digits and one of the `R_a`
     tape uses `a`. Moving every symbol across bijectively would need `a = b`, hence `q = 1`.
4. A slope-1 piece `r(m) → s(m)` is `x ↦ x + (s − r)` in every coordinate. Adding an integer to a
   base-`q` expansion carries, as in `p`-adic addition, so the change can propagate without bound. ∎

**Theorem 3.**
- **Setup.** Let `M` be a reversible 2-counter machine with a configuration `x*`, and let `F_M` be
  as in `ct-z-finite-cycle-problems-are-undecidable`. It lies in `CT_{3,5,7,11,13}(Z)` by that
  node's referee check.
- **The start point.** `n* = Λ(x*) = 3^{a}5^{b}7^{s}` is a configuration code: odd,
  `1 ≤ v_7 ≤ N`, `v_11 = v_13 = 0`.
- **The orbit.** While the run avoids `Halt`, `F_M` multiplies by `7^{t−s}3^{φ_1}5^{φ_2}` and stays
  on configuration codes, where `v_13 = 0`. At a halting configuration `y` it moves to `13Λ(y)`, and
  from there along the forward ray `13^j Λ(y)`, where `v_13 ≥ 1`. Backward-ray codes also have
  `v_13 = 0`.
- **Conclusion.** So the orbit meets `C = 0(13)` iff `M` halts from `x*`. That is undecidable by
  (H): reversible two-counter universality (Morita, TCS 168 (1996)), as used in
  `ct-z-conjugacy-problem-is-undecidable`. With `k` counters the same argument works in `CT_P(Z)`,
  with one prime per counter together with `7, 11, 13`. ∎

**Theorem 4.**
- **Tame ⇒ finite order.** Let `g` permute `𝒫` and be affine on each part, and let `K` be the order
  of the induced permutation. Then `g^K` maps each part `r(m)` onto itself by an affine bijection.
  Its slope is positive (class-wise order preserving), hence `1`, so it is `x ↦ x + tm`.
  - Class transpositions `r_1 + m_1 t ↔ r_2 + m_2 t` with `0 ≤ r_i < m_i` satisfy
    `n ≥ 0 ⇔ τ(n) ≥ 0`, and so does every element of `CT(Z)`.
  - A translation by `tm ≠ 0` breaks this at `r` or at `r − m`. So `t = 0` and `g^K = 1`.
- **Finite order ⇒ tame.** The proof of Theorem 2 of
  `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant` gives a permuted partition refining
  one on whose classes every `g^j` is affine. ∎

## What this says

- **(G1) is a question about subgroups.** Is there a finitely presented `CT_P(Z)`, or any finitely
  generated subgroup of `CT(Z)`, with unsolvable torsion problem? A clean test case: **does `2V`
  embed in `CT(Z)`?** By Theorem 1, if `CT(Z)` has decidable torsion problem, then it does not.
- **The dichotomy so far.**
  - **Thin questions are undecidable.** Finite cycles, 21.74(b),(c); conjugacy, 21.73; reaching a
    class, Theorem 3. All come from valuation-coded machines.
  - **Thick questions are open.** Torsion, i.e. tameness, and 21.74(a). They need machines whose
    behavior is uniform on clopen sets.
  - Theorem 2 shows that the standard thick coding, independent digit tapes, is unavailable. The
    rational-base substitute is a new machine model.

## Lesson for general BH

**Shared slope is rigidity; independent coordinates are computation.**
- In `CT_P(Z)` one rational slope acts on all `p`-adic coordinates at once. Brin–Thompson-type
  hosts (`nV`, twisted `SV_G`) have independent coordinates.
- Independent coordinates carry thick, uniform computation: Turing machines and undecidable torsion
  (Belk–Bleak). A shared slope blocks the standard way to do that. What stays available is thin
  computation in valuations, which decides only questions about single orbits.
- **For host choice in BH.** Use product-type hosts when a construction must run a machine uniformly
  on clopen sets, as compilers and wrappers do. Arithmetic hosts are rigid there, a resource when
  an embedding must not leak dynamics.
