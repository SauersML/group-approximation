---
rg: 2
id: ck-maximal-kernel-four-regimes
kind: claim
title: Every maximal kernel of a finitely presented elementary cover lies in one of four normal-structure regimes, and in the congruence regime finite normal generation is exactly a finitely generated ideal with finitely presented simple projective quotient
distinct_from:
  ck-cover-quotient-kernel-dichotomy: that splits maximal kernels only by whether they contain the covering kernel K; this refines the branch K <= M by the level ideal and its congruence layer into three regimes, and adds an exact finiteness equivalence for the congruence regime.
  ck-envelope-level-ideal-screen: that extracts a proper core-separating level ideal from every proper normal subgroup with no finiteness; this uses that screen and proves that in the congruence regime finite normal generation of the kernel is equivalent to finite generation of the level ideal plus finite presentation of the projective group.
  relative-elementary-fng-iff-level-ideal-fg: that concerns relative elementary subgroups E_n(U,I), which can be maximal only when they coincide with the congruence kernel C_I; this concerns the congruence kernels C_I themselves, which are the maximal kernels of the standard regime.
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that is the open existence question; this is an established classification of where any witness can live and an exact reformulation of one regime.
  decidable-group-ring-has-fp-projective-simple-host: that asks for an arbitrary ring containing Z[H]; the congruence regime here forces a QUOTIENT ring of the fixed sandwich ring U, with only the simple core surviving in its units.
---

**ESTABLISHED.** Let `U` be a finitely generated unital associative ring,
`n >= 3`, `Q = EL_n(U)`, and let `rho : Gamma ->> Q` be a surjection from a
finitely presented group, with kernel `K`.

For a normal subgroup `N <| Q` write `I = lev(N)` for its level ideal and

    C_I = { x in Q : x mod I is central in GL_n(U/I) } ,

the congruence kernel of `Q -> PE_n(U/I) := E_n(U/I)/Z(E_n(U/I))`.

Let `M` be a maximal proper normal subgroup of `Gamma`, `L = Gamma/M`,
`N = rho(M)`, `I = lev(N)`. Exactly one of the following holds.

- **(R1) cover layer.** `K` is not contained in `M`. Then `MK = Gamma` and `L`
  is a simple quotient of `K`.
- **(R2) congruence layer.** `K <= M` and `C_I` is not contained in `N`.
  Then `C_I N = Q` and `L` is a simple quotient of `C_I / E_n(U,I)`.
- **(R3) level-zero projective.** `K <= M` and `C_I` is properly contained
  in `N`. Then `L = PE_n(U/I) / Nbar` for a nontrivial proper normal subgroup
  `Nbar` of `PE_n(U/I)` containing no nontrivial root element.
- **(R4) congruence.** `K <= M` and `N = C_I`. Then `U/I` is a simple ring
  and `L = PE_n(U/I)`.

**Killers.** Assume `Gamma` is perfect.
- If `K` has no nonabelian simple quotient (for instance `K` central, or
  solvable), R1 is impossible.
- If `[Q, C_I] <= E_n(U,I)` (relative commutator formula at level `I`),
  R2 is impossible.
- If every nontrivial normal subgroup of `PE_n(U/I)` contains a nontrivial
  root element (root detection), R3 is impossible.

**R1 and R2 are both unstable-`K_2` centrality questions.** Let `Gamma` be a
quotient of `St_n(U)` compatible with `rho`, as in
[[ck-steinberg-marked-cover]].
- If `K_2(n,U) := ker(St_n(U) -> E_n(U))` is central in `St_n(U)`, then `K`
  is central in `Gamma`, and R1 is impossible.
- If `K_2(n,U/I)` is central in `St_n(U/I)`, then the congruence layer
  `C_I/E_n(U,I)` is central in `Q/E_n(U,I)`, and R2 is impossible.

So the three killers reduce to two ring properties of `U` and its quotients.
The first is centrality of rank-`n` unstable `K_2`. The second is root
detection in `PE_n`.

**Exact finiteness in R4.** The following are equivalent.
1. `Gamma` has a finitely normally generated maximal proper normal subgroup
   in regime R4.
2. `U` has a finitely generated two-sided ideal `I != U` such that
   `PE_n(U/I)` is simple and finitely presented.

In (1) the ideal in (2) is `lev(rho(M))` and `Gamma/M = PE_n(U/I)`.

**Chatterji--Kassabov specialisation.** In the setting of
[[ck-steinberg-marked-cover]] (`n = 4`,
`U = Z[T]<p,q>/(p(1-g)q-1)`, `U` finitely presented by
[[universal-sandwich-ring-is-finitely-presented-and-injective]]), the
simple core `S` embeds in `(U/I)^x` in every regime with `K <= M`, by
[[ck-envelope-level-ideal-screen]]. Combining 2 with
[[projective-elementary-fp-kernel-criterion]] (applicable because `U/I` is
finitely presented), regime R4 has a finitely normally generated witness
iff some finitely generated ideal `I` of `U` has
(a) `PE_4(U/I)` simple, (b) `ker(St_4(U/I) -> E_4(U/I))` finitely normally
generated, and (c) `Z(E_4(U/I))` finitely generated.

**Consequence for the hole.** Condition 2 implies
[[ck-envelope-has-a-finitely-normally-generated-maximal-kernel]] outright.
Under the three killers, the hole is **equivalent** to 2. A proof of the
hole that uses only standard normal-structure theory must therefore build a
finitely presented simple quotient ring of `U` carrying the core in its
units and with finitely presented simple rank-four projective elementary
group. That is the projective ring-host wall, restricted to quotients of
`U`. Any other proof must live in a regime where a standard theorem fails:
R1 (a nonabelian simple quotient of the covering kernel), R2 (failure of the
relative commutator formula for `U`), or R3 (level-zero normal subgroups of
`PE_4` over a quotient of `U`).

DERIVATION
[[ck-maximal-kernel-four-regimes-proof]]
