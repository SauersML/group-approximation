---
rg: 2
id: bmw-census-sat-free-klein-chain-certificates-proof
kind: route
title: Klein-chain certificates for 33 census parity kernels, from one lemma on left orders and square-by-square rewriting traces
target: bmw-census-sat-free-klein-chain-certificates
requires: []
artifacts:
  - experiments/bmw-klein-chains-2026-09-17/README.md
  - experiments/bmw-klein-chains-2026-09-17/chains_census_40_30.json
  - experiments/bmw-klein-chains-2026-09-17/chains_census_50_30.json
  - experiments/bmw-klein-chains-2026-09-17/chains_census_40_40.json
  - experiments/bmw-klein-chains-2026-09-17/verify_klein.py
  - experiments/bmw-klein-chains-2026-09-17/verify_census_40_30.log
  - experiments/bmw-klein-chains-2026-09-17/verify_census_50_30.log
  - experiments/bmw-klein-chains-2026-09-17/verify_census_40_40.log
  - experiments/bmw-klein-chains-2026-09-17/kpure.py
  - experiments/bmw-klein-chains-2026-09-17/kpure_40_30_L6.jsonl
  - experiments/bmw-klein-chains-2026-09-17/kpure_50_30_L6.jsonl
  - experiments/bmw-klein-chains-2026-09-17/kpure_40_40_L6.jsonl
  - experiments/bmw-klein-chains-2026-09-17/kpure_30_30_L6.jsonl
  - experiments/bmw-klein-chains-2026-09-17/kp_176.jsonl
  - experiments/bmw-klein-chains-2026-09-17/kp_5030.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_40_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_50_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_40_40.json
---

The proof has three parts:
- one lemma about left orders (§1);
- unique normal forms for `Γ_c` (§2);
- for each listed class, four identities in `Γ_c` (§3).

The identities are checked by rewriting. `verify_klein.py` prints every rewriting step, and the logs
`verify_census_X.log` hold the full traces. Each identity can therefore be checked by reading its trace
against the square list of the class. §4 works two classes out by hand to show the structure.

## 1. The Klein lemma

For `g` in a left-ordered group, write `|g| = max(g, g^{-1})`.

**Lemma 1.** Let `<` be a left order on a group `G`, and let `a, b ∈ G` with `b ≠ 1` and
`a b a^{-1} = b^{-1}`. Then `|b| < |a|`.

*Proof.*
1. **Reductions.**
   - The hypothesis is invariant under `b ↦ b^{-1}`. Inverting it gives `a^{-1} b a = b^{-1}`, so it is
     also invariant under `a ↦ a^{-1}`. So assume `b > 1` and `a ≥ 1`.
   - `a ≠ 1`, since otherwise `b² = 1`, which is impossible in a left-ordered group (`b > 1` gives
     `b² > b > 1`). Likewise `a ≠ b`, since otherwise `b = b^{-1}`.
2. **`a < b` is impossible.** Suppose `a < b` and put `g = b^{-1} a`.
   - Left multiplication by `b^{-1}` gives `g < 1`, so `g² < g < 1`.
   - From `a b^{-1} = b a` we get `g² = b^{-1}(a b^{-1}) a = a²`.
   - But `a > 1` gives `a² > 1`, a contradiction.
3. **Conclusion.** So `a > b > 1 > b^{-1}`, and `|b| = b < a = |a|`. ∎

**Corollary 2.** Suppose `x_1, …, x_k` are nontrivial elements of `G` and `x_{i+1}` inverts `x_i` for
every `i` (indices mod `k`). Then `G` is not left-orderable.

*Proof.* Lemma 1 gives `|x_1| < |x_2| < ⋯ < |x_k| < |x_1|`. ∎

This is the argument of `bmw-40-40-193-281-332-klein-chain-proof` §2, repeated here so the route
stands alone.

## 2. Normal forms

Fix a class `c` of `census_{m}0_{n}0.json`. Its squares give a map `SQ(h, v) = (v', h')`, the
relation `h v = v' h'`. `verify_klein.py` asserts two things about it:
- it is a bijection from the `m·n` pairs `(h, v)` onto the `m·n` pairs `(v, h)`;
- `pA = pB = 0`, so every letter is an involution.

`Γ_c` is presented by the letters, the relations `x² = 1`, and the relations `h v = SQ(h, v)`.

Orient these relations as the rewriting system
`R = {x x → 1 (every letter x), h v → v' h' (every square)}`.

**Termination.** Each rule either shortens the word, or keeps the length and removes one pair
"`h`-letter before `v`-letter". So every rewriting sequence is finite.

**Local confluence.** The overlaps of left-hand sides are of three kinds:
- `x x x`: both ways give `x`.
- `h h v`: one way gives `v`. The other gives `h v' h'`, which must reduce to `v`.
- `h v v`: one way gives `h`. The other gives `v' h' v`, which must reduce to `h`.

`verify_klein.py` checks the last two for every square, before any chain is examined.

**Consequence.** By Newman's lemma, every word has a unique `R`-normal form. It has the shape
(freely reduced `v`-word)(freely reduced `h`-word). Each rule is a defining relation, so two words are
equal in `Γ_c` exactly when their normal forms agree. In particular, a word equals `1` exactly when it
reduces to the empty word. A nonempty freely reduced word in `v`-letters alone, or in `h`-letters
alone, is already a normal form, so it is `≠ 1`.

## 3. The certificates

For each class `c` listed in the claim, `chains_census_X.json` gives four strings `x_1..x_4`. The
string `v…|h…` stands for the `v`-word followed by the `h`-word. `verify_klein.py` checks three things:
1. **Each `x_i` is nontrivial and lies in `Γ_c^+`.** It is a nonempty normal form, so it is
   nontrivial by §2. Its `v`-length and `h`-length are both even, so it lies in `Γ_c^+`. In every
   chain, each `x_i` is a pure word, a `v`-word or an `h`-word of length 2, 4, 6 or 8.
2. **`x_{i+1}` inverts `x_i` for `i = 1..4` (mod 4).** The word
   `x_{i+1} · x_i · x_{i+1}^{-1} · x_i` reduces to the empty word. The trace is printed, one rule
   application per line.
3. **The squares form a bijection, and `R` is locally confluent.** These are the checks of §2.

The command, run from `experiments/bmw-klein-chains-2026-09-17/`, is:

```sh
python3 verify_klein.py ../bmw-census-left-orders-2026-09-17/census_X.json chains_census_X.json --trace
```

for `X ∈ {40_30, 50_30, 40_40}`. Its output is `verify_census_X.log`, which ends with one line
`class c Klein chain of length 4 verified` for each listed class: 1, 7 and 25 lines respectively.

The verifier reads only the census file and the chain file. It shares no code with the search
(`kpure.py`) or with the SAT pipeline. By Corollary 2, applied in `G = Γ_c^+`, each listed parity kernel
is not left-orderable. ∎

## 4. Two chains by hand

Squares are written `hv=v'h'`. For involutions, `h v = v' h` with the same `h` on both sides means
`h v h = v'`, so `h` acts on the `v`-letters by conjugation.

There are two moves.
- **(K)** If `p` commutes with `r` and `s`, and `q` swaps `r ↔ s`, then `pq` inverts `rs`.
  Indeed, `pq · rs · qp = p (sr) p = sr`.
- **(C)** Conjugating an inverting pair by a letter gives an inverting pair.

**`40_40` #232.**
- The squares that are not commutations are `h0v3=v3h1`, `h1v1=v2h1`, `h1v2=v1h1`, `h1v3=v3h0`,
  `h2v2=v2h3`, `h3v0=v3h3`, `h3v2=v2h2` and `h3v3=v0h3`.
- The chain is `x_1 = h1h0`, `x_2 = v0v3`, `x_3 = h3h2`, `x_4 = v1v2`. Every step is a single (K):

| step | commuting letter | swapping letter |
|---|---|---|
| `x_2` inverts `x_1` | `v0` commutes with `h0`, `h1` | `v3` swaps `h0 ↔ h1` (`h0v3=v3h1`, `h1v3=v3h0`) |
| `x_3` inverts `x_2` | `h2` commutes with `v0`, `v3` | `h3` swaps `v0 ↔ v3` (`h3v0=v3h3`, `h3v3=v0h3`) |
| `x_4` inverts `x_3` | `v1` commutes with `h2`, `h3` | `v2` swaps `h2 ↔ h3` (`h2v2=v2h3`, `h3v2=v2h2`) |
| `x_1` inverts `x_4` | `h0` commutes with `v1`, `v2` | `h1` swaps `v1 ↔ v2` (`h1v1=v2h1`, `h1v2=v1h1`) |

- The same chain shape `h1h0, v0v3, *, v1v2` also appears in #253, #255, #261–#264, #272, #282 and
  #290, with different third entries.

**`40_30` #55.**
- The squares that are not commutations are `h0v2=v2h1`, `h1v1=v1h2`, `h1v2=v2h0`, `h2v1=v1h1`,
  `h2v2=v2h3`, `h3v0=v1h3`, `h3v1=v0h3` and `h3v2=v2h2`.
- The chain is `x_1 = h3h0`, `x_2 = v2v0v1v2`, `x_3 = h2h1`, `x_4 = v0v1`.
- The letter actions used are:
  - `v2` maps `h0 ↦ h1`, `h1 ↦ h0`, `h2 ↦ h3` and `h3 ↦ h2`. This comes from `h0v2=v2h1`,
    `h1v2=v2h0`, `h2v2=v2h3` and `h3v2=v2h2`, each multiplied on the left by `v2`.
  - `v1` swaps `h1 ↔ h2`.
  - `h3` swaps `v0 ↔ v1`.
  - `v0` commutes with `h1` and `h2`.
  - `h0` commutes with `v0` and `v1`.

| step | how |
|---|---|
| `x_4` inverts `x_3` | (K): `v0` commutes with `h1`, `h2`, and `v1` swaps them |
| `x_1` inverts `x_4` | (K): `h0` commutes with `v0`, `v1`, and `h3` swaps them |
| `x_2` inverts `x_1` | (C) by `v2`: it maps `x_2` to `v0v1 = x_4` and `x_1` to `h2h1 = x_3`, which is the first step |
| `x_3` inverts `x_2` | (C) by `v2`: it maps `x_3` to `h3h0 = x_1` and `x_2` to `x_4`, which is the second step |

- The same chain `h3h0, v2v0v1v2, h2h1, v0v1`, string for string, is the one found for `50_30` #241,
  #242 and #243.

## 5. The search, which the proof does not use

`kpure.py census.json L out.jsonl classes` searches each class for such cycles.
1. It enumerates the pure even words of length at most `L` in each family.
2. It computes all inverting pairs between a `v`-word and an `h`-word. For `a` a `v`-word and `b` an
   `h`-word, `a` inverts `b` exactly when pushing the `h`-word `b^{-1}` through `a` gives output `a`
   and section `b`. There is a symmetric test with the roles of the families exchanged.
3. It looks for a directed cycle in the graph of inverting pairs.

Two even pure words of the same family never form an inverting pair.
- The letters of one family generate a free product of `Z/2`'s, in which the even words form a free
  subgroup.
- In a free group, no nontrivial element is conjugate to its inverse.

Hence cycles alternate between families.

**Scan results.**
- All candidate classes of `30_30`, `40_30`, `50_30` and `40_40` were scanned at `L = 6`. The results
  are in `kpure_X_L6.jsonl`.
- `40_40` #176 was scanned at `L = 8` and needs a word of length 8 (`kp_176.jsonl`).
- `50_30` #470 has no cycle at `L = 8` (`kp_5030.jsonl`).
- The chains in `chains_census_X.json` are the cycles found.
