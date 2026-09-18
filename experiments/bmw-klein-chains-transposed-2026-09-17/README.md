# Klein-power chains in BMW parity kernels, all census patterns (w7-107, 2026-09-18)

This directory extends `../bmw-klein-chains-2026-09-17/` in two ways:
- to census patterns with transposed letter pairs (`pA > 0` or `pB > 0`);
- to a stronger certificate that also allows power steps.

The proof is `research/bmw-census-klein-power-chain-certificates-proof.md`. No SAT solver is involved.
All commands below run from this directory. The census files are read from
`../bmw-census-left-orders-2026-09-17/`.

## Criterion

In a left-ordered group, write `|g| = max(g, g^{-1})`. Two facts hold:
- **(K)** `a b a^{-1} = b^{-1}` with `b ≠ 1` implies `|b| < |a|`;
- **(P)/(R)** `|r^e| ≤ |r^f|` whenever `1 ≤ |e| ≤ |f|`.

So a cycle `x_0 → x_1 → ⋯ → x_0` refutes left-orderability if:
- each step is either an inverting step (`x_{i+1}` inverts `x_i`) or a power step (`x_i = r^e`,
  `x_{i+1} = r^f`, `|e| < |f|`);
- and at least one step is inverting.

Power steps are what let the certificate reach Promislow-type configurations, where an element
inverts `x²` but not `x`.

## Certificates

**Chain files.**
- `chains_X.json`, one per pattern `X`, lists the classes with a certificate.
- The entry for a class is one of the following:
  - a list of normal forms `v…|h…`;
  - `{"chain": [...], "roots": {"i": r}}`, where step `i` (from `x_i` to `x_{i+1}`) is a power step
    with common root `r`.
- `chains_50_30_470.json` is the certificate for `50_30` #470.

**Checker.** `verify_klein2.py census.json chains.json [--trace]` reads only the census file and the
chain file. It checks:
1. `iA` and `iB` are involutive with `pA` and `pB` transposed pairs, the square map is a bijection, and
   the rewriting system `{x x^{-1} → 1, h v → v' h'}` is locally confluent (overlaps `h h^{-1} v` and
   `h v v^{-1}`), so normal forms are unique;
2. every `x_i` and every root is a nonempty normal form with even `v`- and `h`-length, hence a
   nontrivial element of `Γ^+`;
3. every step is (K), (P) or (R), each checked by reducing a word to `1`, and at least one step is (K).

With `--trace` it prints every rewriting step.

**Logs.** `verify_X.log` is the `--trace` output for `chains_X.json`, and `verify_50_30_470.log` is
the one for #470. Each log starts with its command line.

**Cross-check.** `crosscheck2.py census.json chains.json` re-checks every step with a second
normal-form algorithm, which pushes letters through the `h`-suffix by the square table. All
certificates pass both checks.

## Search

The search does not enter the proofs.

**`kpure2.py census.json L out.jsonl classes|all|cand [--cand out_X.jsonl] [--powers]`** generalises
`kpure.py` to transposed letters.
- Pure words are freely reduced with respect to `iA` / `iB`.
- An inverting pair (`a` inverts `b`) is detected by pushing one pure word through the other, using the
  square map `h v = v' h'` in both directions (`VH(iB[v'], h) = (h', iB[v])`).
- Inverting pairs only join a `v`-word to an `h`-word. The even words of one family form a
  torsion-free subgroup of a free product of cyclic groups, hence a free group, and in a free group no
  nontrivial element is conjugate to its inverse.

With `--powers`:
- the graph's nodes become classes `{x, x^{-1}}`, keyed by (root `r` up to inversion, exponent `k`);
- power edges `r^k → r^{k'}` (`k < k'`) are added;
- a directed cycle is then a certificate.

`collect.py census.json chains.json kpp.jsonl…` turns the cycles found into chain files. Consecutive
entries of the same family become (R) steps, with the root recomputed.

**Runs.** The candidates are the classes with `finH` or `finV` null in `out_X.jsonl`.
- `run_P6.sh` and `resume_P6.sh`: `--powers` scan at `L = 6`, giving `kpp2_X_L6.jsonl`. `resume_P6.sh`
  re-runs unfinished patterns in chunks of 20 classes.
- `kpp2_red_X_L6.jsonl`: `--powers` at `L = 6` on the eleven reducible "Promislow-type" classes of
  `bmw-degree-44-53-parity-kernels-not-left-orderable`, which are refuted at SAT radius 4.
- `kpp2_31_30_L8.jsonl`, `kpp2_31_31_L8.jsonl`: `--powers` at `L = 8`. The single candidates of
  `31_30` (#26) and `31_31` (#12) have no pure inverting pair at all, up to length 8.
- `kpp_470.jsonl`: `--powers` at `L = 8` on `50_30` #470. It found a 6-cycle with two power steps,
  which is `chains_50_30_470.json`.

**Results.** 167 of the 681 candidate classes have a certificate, and so do the reducible classes
`41_40` #1174 and `41_41` #486, #541. `verify_klein2.py` and `crosscheck2.py` both pass all 171
certificates, #470 included. The per-pattern table is in `research/bmw-census-klein-power-chain-certificates.md`.
