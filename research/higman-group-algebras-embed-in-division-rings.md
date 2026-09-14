---
rg: 2
id: higman-group-algebras-embed-in-division-rings
kind: claim
title: Group rings of Higman's group over every division ring embed in division rings, so its linear automata over finite fields are surjunctive
distinct_from:
  linear-sterility-does-not-obstruct-division-embedding: that uses the characteristic-zero division embedding of Fisher--Sanchez-Peralta Proposition 3.14 to separate linear sterility from embeddability; this proves the embedding over every division ring, including positive characteristic, which is where finite-alphabet automata live.
  higman-group-is-sofic: soficity would give stable finiteness of the group algebras (Elek--Szabo); this proves stable finiteness and linear surjunctivity without deciding soficity.
  higman-group-nonsurjunctive: that asks for any strict automaton on Higman's group; this kills the linear ones over every finite field, so a witness must be nonlinear.
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

**ESTABLISHED** by [[higman-group-algebras-embed-in-division-rings-proof]]. Not yet independently re-derived.

Let `H = <a,b,c,d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2>` be Higman's group. For every division ring `k`,
in every characteristic:

1. `k[H]` embeds in a division ring;
2. hence `M_n(k[H])` is directly finite for every `n >= 1`: `BA = I_n` implies `AB = I_n`;
3. for every finite field `F_q` and `n >= 1`, every injective `F_q`-linear cellular automaton on `(F_q^n)^H` is
   surjective.

**Consequences.**
* It refutes [[higman-group-algebra-not-stably-finite]].
* The route `higman-stable-finiteness-failure-gives-nonsurjunctivity` can never fire.
* A Gottschalk counterexample on `H` must be a nonlinear strict automaton.
* The same holds for the four Baumslag--Solitar amalgam vertex groups, and for every subgroup of `H`.
