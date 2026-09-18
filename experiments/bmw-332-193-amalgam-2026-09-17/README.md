# Invariant-subtree quotients of 40_40#332 and #193: the amalgam model and its obstruction

Lane w5-107 (flagship-2026-09-17). Nodes:
`bmw-332-193-self-similar-certificates-need-new-relation` (obstruction) and
`bmw-40-40-332-irreducible-if-dual-orbit-parity` (reduction).

All four automaton groups `K` are in `aut.py` (`AUT[nm] = (out, sec)`, with `a(xw) = out[a][x] sec[a][x](w)`),
copied from `selfrep.build` / `klev.py` of `experiments/bmw-census-left-orders-2026-09-17`.
`checkaut.py` (`checkaut.log`) confirms that `aut.py` equals what `selfrep.build` returns, for both
classes and both sides. `agrp.py` is the exact word problem (`AG.trivial` explores all sections; `None` only on cap overflow,
which never occurred here).

| group | D-letters | tau | amalgam `A` | missing letter of `G_1` |
|---|---|---|---|---|
| 332V | 0,1,2 (`a_2 = a_0a_1`) | 3 | `V_4 * C_2` | 3 |
| 332H | 0,1,2 | 3 | `C_2^3 *_{<c>} S_3`, `c = a_0a_1a_2`, `(τc)^3 = 1` | 3 |
| 193V | 0,1,2 | 3 | `C_2^3 *_{<c>} S_3` | 1 |
| 193H | 0,1,3 | 2 | `C_2^3 *_{<c>} S_3`, `(x_0x_1x_3x_2)^3 = 1` | 1 |

## Files

**Short relations and G_1.**
- `amalg.py nm 12 A12_nm.g` enumerates every cyclically reduced word of length at most 12, up to
  rotation and reversal, and keeps those that are exactly trivial in `K`. Logs: `amalg12_*.log`.
  - Counts: 603 relations for 332V and 242 for each of the others.
  - It also writes `G1w`: the 0-sections of the Schreier generators of `St_K(0)`.
- `A12_nm.g` is the GAP file it produced. It contains `A_12 = <letters | those relations>` and the
  subgroup `G1`.

**The amalgam model.** `amnf.py` has the normal-form word problem in `A`; `amnf.log` holds its output.
It checks exactly that:
1. every one of the relations above is trivial in `A` (0 exceptions in all four);
2. the defining relations of `A` hold in `K`;
3. `ρ : A → S_3` is a homomorphism (see below), `ρ(G_1)` fixes a point `p`, and the missing letter moves `p`;
4. `relsec`: all sections of the defining relators are trivial in `A`, so the wreath recursion
   descends to `A`.

**Index 3 in A.**
- `lowidx.g` reads `A12_nm.g` and runs `LowIndexSubgroupsFpGroup(A_12, G1, 9)`; the result is `lowidx.log`.
- In all four cases exactly one proper subgroup of index at most 9 contains `G1`. It has index 3
  and does not contain the missing letter.
- Its coset action is the map `ρ` that `amnf.py` uses.

**The section chain inside A.**
- `achain.g` computes `G_{k+1} = φ_0(St_{G_k}(0))` by coset enumeration in `A` (via `R`). Drivers
  `ch_nm.g`, logs `achain_nm.log`.
- In every case `[A : G_k] = 3^k` for `k ≤ 6` (332H) or `k ≤ 5` (the other three). Every `G_k` is
  transitive on level 1, and there is no containment `G_j ≤ G_k`.

**ρ is not a congruence quotient.**
- `fac.py` writes `fac332H.g`, and GAP gives `fac332H.log`: `|<(K_n, ρ)>| / |K_n| = 6, 3, 3, 3, 3` for
  `n = 1..5`.
- So `ρ` does not factor through the level-`n` quotient `K_n` for any `n ≤ 5`.
- This is why "the missing letter lies in `G_1` modulo level `n`" holds (`selfrep.py`, earlier lane)
  while it fails exactly in `A`.

**The dual transducer of 332V.**
- `dual.py 332V` prints `B`, the dual transducer of `K(332V)`, and its orbit sizes on levels 1–8;
  output in `dual332V.log`. `B` is transitive on each of those levels (orbit `3^n`).
- `bH.py` writes `bH.g`, and GAP gives `bH.log`: `φ_v(St_B(v)) = B` modulo levels 1–5, for
  `v = 0, 1, 2`.
- `bobs.py 8 2` writes `bobs_8_2.g`; the GAP output is appended to `bobs_8_2.log`.
  - It finds the 34 relations of `B` of length at most 8, all of them consequences of
    `c_1^2 = c_2^2 = (c_1c_2)^2 = 1` with `c_i = b_ib_0^{-1}`.
  - In `A_B = <b | those relations>`, the group `H = φ_2(St_B(2))` lies in an index-3 subgroup
    that does not contain `c_1`. So `B` is self-replicating exactly only if `B` has a relation of
    length at least 9 outside `A_B`.
- `bc1.py L N` is a depth-first search over words `g` in `b_0^{±1}, c_1, c_2, c_3` with `g(2) = 2`,
  looking for `g|_2 ≡ c_1` or `b_1` modulo level `N`. There are no hits for `L = 13`, `N = 4`,
  which is consistent with the obstruction above.
- `parreg2.py`: the largest `B`-invariant set of even-`a_0`-count sequences, iterated as a regular
  language. This is a dead end: the minimal automata grow 2 → 12 → 648 → out of memory at 2 GB
  (`parreg2.log`).

## Conventions
- `amalg.py` and `agrp.py` act right-first (the last letter acts first). `achain.g` acts left-first,
  which is the action of `K^op`: the same set of tree automorphisms, since all letters are involutions.
- Levels and letters are 0-based in Python and 1-based in GAP permutations.

## Reproduce
`python3 amalg.py 332H 12 A12_332H.g` takes about 1 minute per group.
`python3 amnf.py; python3 -c "import amnf; print(amnf.relsec('332H'))"`.
In GAP: `FN:="A12_332H.g";; TL:=4;; N:=9;; Read("lowidx.g");` and `gap -q ch_332H.g`.
`python3 fac.py 332H "[[0,1,2],[0,2,1],[0,1,2],[1,0,2]]" 5 > fac332H.g` (then run it with the
`Print` loop in GAP).
