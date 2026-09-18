---
rg: 2
id: zaremsky-2-16-lehnert-conjecture
kind: claim
title: "Zaremsky Problem 2.16 resolved: for a cloning system on finite groups, is T(G_*) co-context-free, and does it embed in V?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 16, verbatim:
"(Added 2/10/24) Lehnert's conjecture: Every group with context-free co-word
problem embeds in Thompson's group V. So, question, given a cloning system on a
family of finite groups Gn, is the Thompson-like group T(G∗) coCF and/or does it
embed into V?"

This claim is the question. It is established only through an answer route
(never a `requires: []` route into this claim):

- **Q2 yes, hence Q1 yes**: `zaremsky-2-16-by-embedding` requires
  `cloning-system-groups-on-finite-groups-embed-in-v`.
- **Q1 yes and Q2 no**: `zaremsky-2-16-by-cocf-not-in-v` requires
  `finite-cloning-system-groups-are-locally-cocf` and
  `some-finite-cloning-system-group-does-not-embed-in-v`.
- **Q1 no, hence Q2 no**: `zaremsky-2-16-by-not-cocf` requires
  `some-finite-cloning-system-group-is-not-locally-cocf`.

## Reading

- *Cloning system*: in the sense of Witzel–Zaremsky, arXiv:1405.5491 (Groups
  Geom. Dyn. 12 (2018)), surveyed in Zaremsky, arXiv:1606.08762: groups `G_n`,
  homomorphisms `ρ_n: G_n → S_n`, injective maps `ι_{m,n}` and cloning maps
  `κ^n_k: G_n → G_{n+1}` satisfying (C1)–(C3). `T(G_*)` is the group of classes
  `[T_-, g, T_+]` of pairs of `n`-leaf trees and `g ∈ G_n` modulo expansion.
  "Finite groups" means every `G_n` is finite. The question does not say binary
  or `d`-ary; this root reads it as binary cloning systems, and a `d`-ary version
  is recorded separately if a lane pursues it.
- *coCF*: a finitely generated group whose co-word problem (words over a finite
  monoid generating set representing nontrivial elements) is a context-free
  language; this does not depend on the generating set (Holt–Rees–Röver–Thomas,
  J. London Math. Soc. 71 (2005)). `T(G_*)` need not be finitely generated, so
  **Q1** is read as: for every cloning system on finite groups, every finitely
  generated subgroup of `T(G_*)` is coCF ("locally coCF"). For finitely
  generated `T(G_*)` this is exactly "coCF", because coCF passes to finitely
  generated subgroups.
- **Q2**: for every cloning system on finite groups, does `T(G_*)` embed in `V`?
- Model tests: `G_n = S_n` with the standard cloning gives `V` (coCF by
  Lehnert–Schweitzer, arXiv:math/0507090; in `V`). `G_n` trivial gives `F`;
  `G_n = Z/n` gives `T`. Both answers are "yes" there.
- Implications between the parts: `V` is coCF and coCF passes to finitely
  generated subgroups, so Q2 yes gives Q1 yes, and Q1 no gives Q2 no. A
  finitely generated `T(G_*)` that is coCF but embeds in no `V` refutes
  Lehnert's conjecture `lehnert-conjecture-every-cocf-group-embeds-in-v`; that is
  why the question is asked. Settling Lehnert's conjecture alone settles neither
  Q1 nor Q2.

## Known results (abstracts read 2026-09-13 unless noted; each import still needs a verified `-citation` route)

- Lehnert–Schweitzer, arXiv:math/0507090: the Higman–Thompson groups, in
  particular `V`, have context-free co-word problem.
- Lehnert (thesis): `V ≤ QAut(T_{2,c})`, conjectured universal coCF.
  Bleak–Matucci–Neunhöffer, arXiv:1312.1855 (J. London Math. Soc. 94 (2016)):
  `QAut(T_{2,c})` embeds in `V`, so the conjecture becomes "a group is coCF iff
  it is a finitely generated subgroup of `V`".
- Berns-Zieve–Fry–Gillings–Hoganson–Mathews, arXiv:1407.7745: the groups
  `V_(G,θ)` (`G` finite, `θ` an endomorphism) are coCF, proposed as potential
  counterexamples. Bennett, PhD thesis (St Andrews, 2018), "On plausible
  counterexamples to Lehnert's conjecture": a subclass of that family embeds in
  `V`.
- Farley, arXiv:1406.4590: groups determined by finite similarity structures
  (FSS) are coCF under a mild extra hypothesis; a subfamily is proposed as
  potential counterexamples.
- Bodart–D'Angeli–Perego–Rodaro, arXiv:2608.02111 (Aug 2026): a finitely
  generated group embeds in `V` iff it admits a faithful context-free action
  (class CF-TR); the abstract says all known coCF groups embed in `V`.
- Jaspars, arXiv:2608.01168 (Aug 2026): a group embeds in `V` iff it has finitely
  many context-free subgroups whose cores intersect trivially.
- Bishop–Bodart–Issini–Perego, arXiv:2601.13058 (Jan 2026): period growth of
  coCF groups.
- Open-status check (z-status-b, 2026-09-13, bounded to arXiv and web search):
  no answer to Q1 or Q2 and no proof or refutation of Lehnert's conjecture found.

## Attempts

- 2026-09-13 (z2-16-lehnert), in progress:
  1. Embedding side: realize `T(G_*)` on finitely many transitive sets with
     context-free Schreier graphs (Jaspars' criterion), or conjugate its natural
     Cantor-space action into prefix replacements. Test on signed permutations
     with twisted cloning (a flip on a cone becomes a prefix replacement after
     the difference recoding `x ↦ (x_1, x_1+x_2, x_2+x_3, …)` mod 2) and on direct
     powers `A^n` with diagonal cloning (`T = LC(C, A) ⋊ F`, acting on `C × A`).
  2. Obstruction side: pure systems (`ρ_n` trivial) give `T = K ⋊ F` with `K` a
     locally finite directed union of the `G_n`. If coCF bounds period growth,
     a cloning system whose clones multiply to elements of very large order in
     short words would answer Q1 no. Which bound arXiv:2601.13058 proves is
     being checked.
- 2026-09-17 (sw-101), resolution proposed: **Q1 no and Q2 no**. The obstruction
  comes from *undecidability*, not from period growth.
  - Construction: the claim `finite-cloning-groups-realize-every-lamplighter-over-thompson-f`,
    with complete proof in the route `finite-cloning-lamplighter-realization-proof`.
    For any `H ≤ F`, take `G_n = (Z/2)^{D_n}` with `D_n = ⊔_{j≤n} Trees_j/H`, and let the
    cloning maps push functions forward along caret attachment. This is a properly graded
    pure cloning system on finite groups, and `T(G_*)` contains a lamp `t` with
    `C_F(t) = H`.
  - Witness: take `H = ⟨x_0^i y x_0^{-i} : i ∈ S⟩` with `S` non-recursive. Then the words
    `[t, x_0^i y x_0^{-i}]` encode `S`, so the word problem of the finitely generated group
    `T(G_*)` is unsolvable. Hence `T(G_*)` is not coCF and does not embed in `V`.
  - Routes: `finite-cloning-group-with-undecidable-lamp-stabilizer` and
    `finite-cloning-undecidable-lamp-stabilizer-not-in-v`. These close
    `zaremsky-2-16-by-not-cocf`.
  - Not an artefact of non-computable input: `computable-finite-cloning-group-not-cocf-not-in-v`
    takes `S` recursive but not decidable in time polynomial in `i`. The cloning data are
    then computable and `⟨x_0, x_1, t⟩` has solvable word problem, yet it is not coCF and not
    in `V`, because coCF word problems are decidable in polynomial time (CYK). So any
    positive answer must restrict the class of cloning systems by a complexity condition.
  - The construction does not bear on Lehnert's conjecture. It awaits a referee.
