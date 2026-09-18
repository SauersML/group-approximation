---
rg: 2
id: strongly-shift-similar-point-stabilizers-are-copies-of-the-group
kind: claim
title: In a strongly shift-similar group every point stabilizer, and every pointwise stabilizer of a finite set, is isomorphic to the group itself
requires:
  - houghton-like-groups-are-strongly-shift-similar
distinct_from:
  houghton-like-groups-are-strongly-shift-similar: that imports the Mallery-Zaremsky facts (psi_j surjective, H_1(G) = G, H_n(G) contains FSym); this derives from them that stabilizers of finite sets are copies of G.
  fp-strongly-shift-similar-admits-type-a-action: that is Zaremsky's type (A) theorem for finitely presented strongly shift-similar groups; this is the elementary stabilizer computation behind finiteness statements of that kind.
---

**ESTABLISHED** (lane proof, elementary, proved below; not independently reviewed; no priority claimed, it is
probably folklore among the source's readers).

**Setting.** `G <= Sym(N)` is strongly shift-similar (Mallery--Zaremsky arXiv:2202.00822, Definition 3.17). For
`j in N` let `s_j : N -> N \ {j}` be the increasing bijection and
`psi_j(g) = s_(g(j))^-1 ∘ g|_(N\{j}) ∘ s_j`, as in `houghton-like-groups-are-strongly-shift-similar`.

**Statement.**
1. `FSym(N) <= G`.
2. For every `j`, `psi_j` restricts to an isomorphism `Stab_G(j) -> G`.
3. For every finite set `F ⊂ N`, the pointwise stabilizer `Stab_G(F)` is isomorphic to `G`. In particular it is
   finitely generated (finitely presented) whenever `G` is.
4. The same holds for `H_n(G)` acting on `[n] x N`, for every `n >= 1`: stabilizers of finite sets are copies of
   `H_n(G)`.

**Proof.**
1. `G = H_1(G)` (Proposition 5.3) and `H_1(G)` contains `FSym([1] x N)` (the source's proof of Proposition 5.5).
2. On `Stab_G(j)` we have `psi_j(g) = s_j^-1 g s_j`, a homomorphism, and it is injective because `g` is determined
   by its restriction to `N \ {j}` and fixes `j`. For surjectivity let `h in G`. By Lemma 3.19, `h = psi_j(g)` for
   some `g in G`. Put `k = g(j)` and let `f = (j k)` (or `f = 1` if `k = j`); `f in G` by item 1. Then
   `fg in Stab_G(j)`, and since `g` maps `N\{j}` onto `N\{k}` and `f` maps `N\{k}` onto `N\{j}`,

       psi_j(fg) = (s_j^-1 f|_(N\{k}) s_k) (s_k^-1 g|_(N\{j}) s_j) = phi · h,

   where `phi = s_j^-1 f|_(N\{k}) s_k` moves only finitely many points. Conjugation by `s_j` maps the finitary
   permutations of `N` fixing `j` onto `FSym(N)`, and those lie in `Stab_G(j)` by item 1. So `phi^-1` and hence
   `h = phi^-1 psi_j(fg)` lie in `psi_j(Stab_G(j))`.
3. Induction on `|F|`: if `j in F`, then `psi_j` carries `Stab_G(F)` isomorphically onto `Stab_G(s_j^-1(F\{j}))`.
4. `H_n(G)` has a strongly shift-similar representation on `N` (Proposition 5.5), and the representation is
   induced by a bijection `[n] x N -> N`, so apply items 1–3 to it. ∎

**Use.** For `n >= 2` and `G` finitely generated, every stabilizer of a finite subset of `[n] x N` in `H_n(G)` is
finitely generated (Corollary 5.11). This feeds `finitary-mixing-of-fp-highly-transitive-groups-is-fp` and
`fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`.

**Calibration (these stabilizer facts do not by themselves give finite presentation).** Houghton's `H_2 = H_2(FSym)`
contains `FSym`, is highly transitive, has `H_2 / FSym ≅ Z` finitely presented, and by item 4 all its finite-set
stabilizers are copies of `H_2`, hence finitely generated. Yet `H_2` is not finitely presented (K. S. Brown,
recalled in the Mallery--Zaremsky source). So any finiteness theorem for these groups needs more than
"finitely presented germ quotient plus finitely generated stabilizers".
