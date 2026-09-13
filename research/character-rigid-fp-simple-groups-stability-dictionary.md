---
rg: 2
id: character-rigid-fp-simple-groups-stability-dictionary
kind: claim
title: A character-rigid finitely presented infinite simple group is sofic iff it is not permutation stable, and hyperlinear iff it is not HS-stable
distinct_from:
  thompson-v-sofic-iff-not-permutation-stable: that is the Hamming dictionary for V alone; this states it for every finitely presented infinite simple group whose only extreme characters are trivial and regular, and adds the normalized-Hilbert--Schmidt dictionary.
  thompson-v-ce-one-word-trace-face-is-binary: that is a support-value law for one word of V; this is a stability equivalence for the whole class, in both the permutation and the unitary setting.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that is one direction for any finitely generated group; this adds the converse for character-rigid simple groups.
artifacts:
  - research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md
---

**ESTABLISHED.** Let `Γ` be a finitely presented infinite simple group whose only extreme
normalized characters are `τ_triv` and `τ_reg`, so every normalized character is
`t τ_reg + (1-t) τ_triv` with `t` in `[0,1]`.

**(P) Permutations.** The following are equivalent, with Bradford's definitions
(arXiv:2211.15249v2, Definitions 1.1–1.3 and Remark 1.4, quoted in the artifact §2):
1. `Γ` is not sofic;
2. `Γ` is stable;
3. `Γ` is weakly stable;
4. `Γ` is locally stable;
5. `Γ` is weakly locally stable;
6. every almost-homomorphism `φ_n : Γ -> Sym(k_n)` satisfies `d(φ_n(g), id) -> 0` for every `g`.

**(U) Unitaries.** The following are equivalent, for asymptotic representations
`π_n : Γ -> U(d_n)` in the normalized Hilbert--Schmidt norm:
1. `Γ` is not hyperlinear;
2. `Γ` is strictly HS-stable;
3. `Γ` is flexibly HS-stable, as in `hyperlinear-flexibly-hs-stable-group-is-residually-finite`;
4. every asymptotic representation satisfies `||π_n(g) - 1||_2 -> 0` for every `g`.

So for these groups soficity (hyperlinearity) is decided by one question: is there one
almost-homomorphism (asymptotic representation) that does not collapse to the trivial one
on some fixed element? By amplification, any fixed positive amount of non-collapse on one
element is enough.

**Instances.**
- **Thompson's `V`**, by `thompson-v-character-simplex` and
  `thompson-v-finitely-presented-infinite-simple`. For `V`, (P) is
  `thompson-v-sofic-iff-not-permutation-stable`, and (U) is new here in this form.
- **Thompson's `T`**, provided `T` is finitely presented, infinite and simple (classical,
  Cannon--Floyd--Parry; not re-read in this repository). Its character rigidity is item 4 of
  `no-proper-character-groups-avoid-amenable-orbit-full-groups`, which assumes the same
  simplicity. So, under that classical input, `T` is sofic iff it is not permutation stable,
  and hyperlinear iff it is not HS-stable. This instance is not claimed ESTABLISHED here.
- **Finitely presented alternating full groups `A(G)`** of minimal, purely infinite,
  essentially principal Cantor groupoids, whose character rigidity is item 3 of the same
  node (Gardella--Tanner).

**Also spatial models are excluded** for `V` and `T`
(`thompson-v-cantor-orbits-have-no-folner-sets`, `thompson-t-orbits-carry-no-invariant-means`).
So a non-collapsing almost-homomorphism, whose existence is equivalent to soficity, has to be
non-spatial.

No novelty is claimed. (P) is the argument of `thompson-v-sofic-iff-not-permutation-stable-proof`,
whose final remark already says it covers every non-LEF group with this character simplex. (U) is
its unitary transcription.

Proof: `character-rigid-fp-simple-stability-dictionary-proof`.
