---
rg: 2
id: type-f-benignness-is-embedding-of-the-double
kind: claim
title: "A subgroup N of a type F_m group K is F_m-benign iff the double K *_N K embeds in a group of type F_m; so the two-occurrence window is Zaremsky 1.1 for one torsion-free double"
distinct_from:
  two-occurrence-realizability-is-type-f-benignness: That identifies type F_m Mikhailova triples with F_m-benign relation subgroups and reduces the universal question to N_U; this turns benignness itself into an embedding statement about the double, and places the two-occurrence window inside Zaremsky 1.1.
  every-re-normal-subgroup-of-a-free-group-is-type-f-benign: That is the open universal benignness statement; this proves it is equivalent to embedding one torsion-free finitely generated recursively presented group, the double of F(B) along N_U, in a type F group.
  every-finitely-presented-group-embeds-in-an-f-infinity-group: That asks every finitely presented group to embed in an F_infinity group; this concerns only doubles of free groups along normal subgroups, which are torsion-free and implied by that statement.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Let
`m ∈ {2, 3, ..., ∞}` or `m = F`, let `K` be a group of type `F_m`, and let
`N ≤ K`. Write `D(K, N) = K_1 *_N K_2` for the **double** of `K` along `N`: two
copies of `K` amalgamated along `N` by the identity. `F_m`-benign is as in
`two-occurrence-realizability-is-type-f-benignness`.

1. **Benign iff the double embeds.** `N` is `F_m`-benign in `K` iff `D(K, N)`
   embeds in a group of type `F_m`.
   - If `(Λ, Σ)` is a witness, then `D(K, N)` is the subgroup `<K_1, K_2>` of
     the type `F_m` group `Λ *_Σ Λ`.
   - Conversely, in any host of `D(K, N)`, `Σ = K_2` is a witness for `K_1`.
2. **The witness can be a copy of `K`.** If `N` is `F_m`-benign, then there is a
   witness `(Λ, Σ)` with `Σ ≅ K`. For `K = F(A)` this is a free group of rank `|A|`.
3. **Doubles are harmless.** `D(F(A), N)` is torsion-free. If `N` is
   recursively enumerable, it is finitely generated and recursively presented.
   So the torsion and countability obstructions that separate benignness from
   embeddability of `F/N` (item 4 of `two-occurrence-realizability-is-type-f-benignness`)
   disappear in the double.
   - Example: `N = <<a^2>> ≤ F(a)` gives `D = <a, b | a^2 = b^2>`, the Klein bottle group, of type `F`. `Z/2` itself embeds in no type `F` group.
4. **The two-occurrence window is Zaremsky 1.1 for one double.** Let
   `U = F(B)/N_U` be Higman's universal finitely presented group, and let
   `D_U = D(F(B), N_U)`. The following are equivalent:
   - every finitely generated recursively presented group has a type `F_m`
     Mikhailova triple, which closes the opposite-sign two-occurrence window at level `F_m`;
   - `D_U` embeds in a group of type `F_m`.

   `D_U` is finitely generated and recursively presented, so it embeds in `U`.
   Hence `E_m` (every finitely presented group embeds in a group of type `F_m`,
   `zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`) implies window closure
   at level `F_m`.
5. **Two-occurrence obstructions answer Zaremsky 1.1 negatively.** Suppose that,
   for some `n >= 2`, some finitely generated recursively presented group `G`
   has a word problem that is not inverse-respecting two-occurrence reducible,
   with opposite signs, to the word problem of any group of type `F_{n+1}`.
   Then the torsion-free, finitely generated, recursively presented double
   `D(F, N_G)` embeds in no group of type `F_{n+1}`. So `E_{n+1}` fails, which
   is a negative answer to both parts of Zaremsky Problem 1.1.
   - So no such obstruction can be proved without also proving
     `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`.
   - A word-problem obstruction that is to stay independent of Problem 1.1
     must use the equal-sign pattern `X Q X = Q` or three occurrences. Four
     occurrences are already complete in a type `F` host
     (`type-f-group-receives-re-languages-by-pattern-reductions`).

Proof: route `type-f-benignness-is-embedding-of-the-double-proof`.
