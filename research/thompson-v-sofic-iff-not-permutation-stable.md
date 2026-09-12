---
rg: 2
id: thompson-v-sofic-iff-not-permutation-stable
kind: claim
title: Thompson's V is sofic exactly when it is not permutation stable
distinct_from:
  thompson-v-not-sofic: that is the open nonsoficity question; this identifies it with each of Bradford's four permutation-stability properties of V, without deciding any of them.
  sofic-stable-implies-residually-finite: that is the general one-directional principle that a sofic stable group is residually finite; this adds the converse for V, from its character rigidity, and the local and weak variants.
  thompson-v-ce-one-word-trace-face-is-binary: that is the normalized-HS support law for one word of V; this is the Hamming statement, phrased through permutation stability.
artifacts:
  - research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md
---

**ESTABLISHED.** Use Bradford's definitions (*Local permutation stability*,
arXiv:2211.15249v2, Definitions 1.1–1.3 and Remark 1.4) for almost-homomorphisms
`phi_n : V -> Sym(k_n)`. The following are equivalent for Thompson's group `V`:
1. `V` is not sofic;
2. `V` is stable: every almost-homomorphism is pointwise Hamming-close to homomorphisms;
3. `V` is weakly stable: the same for separating almost-homomorphisms;
4. `V` is locally stable: close to partial homomorphisms;
5. `V` is weakly locally stable.

So `thompson-v-is-sofic` holds exactly when `V` is not permutation stable, in any of the four
senses.

**Flexible P-stability is equivalent too.** Here the correction is by genuine actions on finite
supersets `Y_n >= X_n` with `|Y_n \ X_n| / |X_n| -> 0`, as in
`hyperbolic-rf-not-flexibly-p-stable`.
- Stable implies flexibly stable.
- Conversely, every action of `V` on a finite set is trivial, because `V` is infinite and simple.
  So a flexible correction forces each `phi_n(g)` to fix all but `o(|X_n|)` points, and then no
  separating almost-homomorphism exists.

For `V`, strict and flexible permutation stability coincide.

## Why it matters

- **Bradford's heuristic is not a separate property.** Bradford (p. 4) reads his local
  stability theorem for derived subgroups of full groups of minimal subshifts as "evidence that
  V is stable", and notes that stability would make `V` non-sofic. By this claim, stability of
  `V` *is* nonsoficity of `V`.
- **The negative direction.** A proof must show that every almost-homomorphism of a finitely
  presented group with no finite quotients is close to the trivial one. The stable groups
  Bradford lists are all sofic ("the only groups known to be stable have also long been known to
  be sofic", p. 1), and his IRS criterion is for amenable groups.
- **The positive direction.** One almost-homomorphism in which one element keeps moving a
  non-vanishing proportion of points makes `V` sofic. The character is rigid, and tensor powers
  amplify separation (the one-word form of `thompson-v-not-sofic`).

Derivation: `thompson-v-sofic-iff-not-permutation-stable-proof`.
