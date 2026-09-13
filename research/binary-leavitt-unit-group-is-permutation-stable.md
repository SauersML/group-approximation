---
rg: 2
id: binary-leavitt-unit-group-is-permutation-stable
kind: claim
title: The binary Leavitt unit group is permutation stable, so stability in permutations implies neither soficity nor residual finiteness
distinct_from:
  sofic-stable-implies-residually-finite: that is the principle that a sofic stable group is residually finite; this is a stable group that is not residually finite, which is consistent with that principle only because the group is not sofic.
  openai-leavitt-unit-nonsofic: that is nonsoficity of the same group; this adds that every almost-homomorphism into symmetric groups is asymptotically trivial, using the character simplex.
  thompson-v-sofic-iff-not-permutation-stable: that is the same dichotomy for V, where both alternatives are open; for the Leavitt unit group the nonsofic alternative is established, so the dichotomy resolves.
---

**ESTABLISHED (unreviewed).** Let `H = L_(F_2)(1,2)^x` be the unit group of the binary Leavitt
algebra. Every almost-homomorphism `phi_n : H -> Sym(k_n)`, meaning
`d(phi_n(gh), phi_n(g) phi_n(h)) -> 0` for all `g, h` in normalized Hamming distance, satisfies

```text
d(phi_n(g), id) -> 0      for every g in H.
```

So `H` is permutation stable in each of Bradford's senses (stable, weakly stable, locally stable,
weakly locally stable; *Local permutation stability*, arXiv:2211.15249v2, Definitions 1.1--1.3), and
flexibly stable as well. The correcting homomorphisms are the trivial ones.

## Why it matters

- **A stable group that is not residually finite.** `H` contains Thompson's `V`, which is infinite,
  simple and not residually finite, so `H` is not residually finite. Glebsky--Rivera's principle
  `sofic-stable-implies-residually-finite` needs soficity, and `H` shows that hypothesis cannot be
  dropped.
- **Against the pattern Bradford recorded.** Bradford, arXiv:2211.15249v2, p. 1: "the only groups known
  to be stable have also long been known to be sofic". `H` is a stable group that is not sofic.
  - Any stable nonsofic group postdates the first nonsofic group (2026-08-01), so this is new as far
    as this graph records.
  - The check was bounded to this repository and Bradford's remark. No web search was possible.
- **Maximal rigidity.** `H` has no nontrivial asymptotic permutation models at all. This is the
  Hamming analogue of having no finite quotients, and it is stronger: it holds for every
  almost-homomorphism, not only for genuine actions.

## Mechanism

- **Character.** The fixed-point proportion `chi(g) = lim_omega |Fix phi_n(g)|/k_n` is a character of
  `H`.
- **Character simplex.** By `binary-leavitt-full-character-simplex`, `chi = a 1 + (1-a) delta_1`.
- **`a < 1` is impossible.** Coordinatewise tensor powers would give a separating almost-homomorphism,
  so `H` would be sofic, contradicting `openai-leavitt-unit-nonsofic`.
- **Conclusion.** So `a = 1` along every ultrafilter, which is the displayed limit.

Derivation: `binary-leavitt-unit-group-is-permutation-stable-proof`.
