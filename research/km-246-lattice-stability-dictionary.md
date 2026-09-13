---
rg: 2
id: km-246-lattice-stability-dictionary
kind: claim
title: For q >= 4 the (2,4,6) Kac-Moody lattice is sofic iff it is not permutation stable, and hyperlinear iff it is not HS-stable
distinct_from:
  character-rigid-fp-simple-groups-stability-dictionary: that is the dictionary for every character-rigid finitely presented infinite simple group; this is its instance at S_q, which needed the character rigidity of S_q.
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that gives the permutation half from IRS rigidity alone; this adds the unitary half.
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that is the non-hyperlinear or LLP-failure dichotomy for all Caprace--Remy lattices; this makes non-hyperlinearity of S_q equivalent to HS stability.
---

**ESTABLISHED (unreviewed).** Let `q >= 4` and `S_q` as in
`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`.

**(P) Permutations.** These are equivalent, with Bradford's definitions as in
`character-rigid-fp-simple-groups-stability-dictionary`:
1. `S_q` is not sofic;
2. `S_q` is (weakly, locally, weakly locally) permutation stable;
3. every almost-homomorphism `φ_n : S_q -> Sym(k_n)` satisfies `d(φ_n(g), id) -> 0` for every
   `g`.

**(U) Unitaries.** These are equivalent, for asymptotic representations
`π_n : S_q -> U(d_n)` in the normalized Hilbert--Schmidt norm:
1. `S_q` is not hyperlinear;
2. `S_q` is strictly HS-stable;
3. `S_q` is flexibly HS-stable;
4. every asymptotic representation satisfies `||π_n(g) - 1||_2 -> 0` for every `g`.

**Reading for the open targets.**
- `km-246-lattice-is-sofic` asks for one almost action that does not collapse.
- `hyperlinear-fp-infinite-simple-kazhdan-group`, through `S_q`, asks for one asymptotic
  representation that does not collapse. By amplification, any fixed positive amount of
  non-collapse on one element is enough.
- `non-hyperlinear-group`, through `S_q`, asks to prove that every asymptotic representation
  collapses. For `S_q` this is HS stability, and it is the target of
  `compact-hyperbolic-km-regular-microstates-synchronize`.

Proof: `km-246-stability-dictionary-via-character-rigidity`.
