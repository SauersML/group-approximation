---
rg: 2
id: bmw-a5-parity-obstruction-to-pgl2-tree-models-proof
kind: route
title: Proof via the vertex stabiliser PGL_2(O) acting on the neighbours through PGL_2(F_4) = A_5, and two independent census scripts
target: bmw-a5-parity-obstruction-to-pgl2-tree-models
requires: []
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/parity5.py
  - experiments/bmw-cone-trees-2026-09-18/parity5.log
  - experiments/bmw-cone-trees-2026-09-18/parity5b.py
  - experiments/bmw-cone-trees-2026-09-18/parity5b.json
  - experiments/bmw-cone-trees-2026-09-18/remaining.py
  - experiments/bmw-cone-trees-2026-09-18/remaining.json
---

# Proof

## 1. The lemma

Let `(F, ρ, o)` be a tree model on the h-side (as defined in the claim), with valuation ring `O`,
uniformizer `π` and residue field `k`.

**Valency.** The neighbours of `o` are in bijection with the h-letters, so `Δ` is `m`-regular and
`|k| = m − 1`. For `m = 5`, `k = F_4`.

**The stabiliser acts through `PGL_2(k)`.** After conjugating in `PGL_2(F)` we may take `o = [O²]`.
- Its stabiliser is `F^* GL_2(O) / F^*`.
- The neighbours of `o` are the lattices `L` with `π O² ⊊ L ⊊ O²`. These correspond to the lines in
  `O²/π O² = k²`, that is, to `P^1(k)`.
- `g ∈ GL_2(O)` acts on the neighbours through its reduction `ḡ ∈ GL_2(k)` acting on `P^1(k)`. That
  action factors through `PGL_2(k)`.

So the permutation of the neighbours induced by any element of `Stab(o)` lies in the image of
`PGL_2(k) → Sym(P^1(k))`.

**`PGL_2(F_4)` acts by even permutations.**
- Every element of `F_4^*` (a group of order 3) is a square. Hence `GL_2(F_4) = F_4^* SL_2(F_4)`, and
  `PGL_2(F_4) = SL_2(F_4)`.
- `SL_2(F_4) ≅ A_5` is simple and non-abelian.
- The sign character `PGL_2(F_4) → Sym(P^1(F_4)) → {±1}` is a homomorphism to an abelian group, so it
  is trivial.

**Conclusion.** Let `u` be a v-letter, and let `h v = u h'` be any square whose third letter is `u`.
- Then `ρ(u) ρ(h') o = ρ(h) ρ(v) o = ρ(h) o`, because `ρ(v)` fixes `o`.
- So `ρ(u) ∈ Stab(o)` sends the neighbour `ρ(h') o` to `ρ(h) o`.
- Under the bijection `h ↦ ρ(h) o`, the permutation induced by `ρ(u)` is therefore `π_u`, which must be
  even. ∎

For `m = 3` and `m = 4`, `PGL_2(F_2) ≅ S_3` and `PGL_2(F_3) ≅ S_4` act on the 3 and 4 points of
`P^1` as the full symmetric groups. So every local action is realised locally and there is no
constraint. (For `q = 3` the action map `PGL_2(F_3) → S_4` is injective, and both groups have
order 24.)

**Mixed characteristics.** If both sides have tree models in one field `F`, for two discrete
valuations with residue fields `F_{q_1}` and `F_{q_2}` of different characteristics, then
`char F = 0`. A field of characteristic `p > 0` has every residue field of characteristic `p`. This is
the remark on `(4,3)`: the residue fields `F_3` and `F_2` force characteristic 0.

## 2. The count

`remaining.py` lists the census classes of
`experiments/bmw-census-left-orders-2026-09-17/out_<pattern>.jsonl` with `finH` or `finV` equal to
`None`, that is, without an irreducibility certificate. It then removes those with a Klein-power or
Klein-frame certificate:
- `chains_*.json` of `experiments/bmw-klein-chains-2026-09-17` and
  `experiments/bmw-klein-chains-transposed-2026-09-17`;
- the classes of `bmw-klein-frame-chain-certificates` and `bmw-klein-free-quaternionic-parity-kernels`,
  entered by hand.

This leaves 994 classes, 374 of them of degree `(5,3)`.

For each `(5,3)` class and each v-letter `u`, both scripts compute `π_u` and its sign.
- `parity5.py` uses `localact.maps` of the census directory.
- `parity5b.py` reads the squares directly from `census_<pattern>.json`, checks that each `π_u` is a
  bijection, and compares its verdict with `parity5.json`.

Both find 306 classes with an odd `π_u`. `parity5b.py` prints
`374 classes; 306 with an odd v-letter; agreement with parity5.json: 374`. `parity5b.json` records,
for each class, the first odd letter and the cycle type of every `π_u`, so each exclusion can be
checked by hand from a single square set.

The local action groups of the 68 even classes have orders 2, 4, 6, 10, 12 and 60 (`parity5.log`),
all of them subgroups of `A_5`.
