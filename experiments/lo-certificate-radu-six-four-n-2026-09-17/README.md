# Radu's (6,4n)-groups: the simple subgroup is the index-4 parity kernel and is not left-orderable

Supports `research/radu-six-four-n-simple-lattices-are-not-left-orderable.md` and its proof.

**Source.** N. Radu, *New simple lattices in products of trees and their projections*,
arXiv:1712.01091v3. The scripts read the square datum from the pstricks source of Figure
`picture:64n`, file `Lattices3ALL.tex` (sha256
`d25c2f5005704d1f17c428b61fd934d0593a5e30e5eeae021a532f6447948f38`). The TeX is not included; set
`RADU_TEX` to its path.

**Requirements.** Python 3 and GAP 4. All GAP runs are single-threaded and fit in `-o 2g`.

## Files

| file | purpose |
| --- | --- |
| `bmw.py` | VH-datum checker `BMW` and `RADU_44`, the four `Γ_{4,4}` squares (same as in `experiments/lo-certificate-radu-lattices-2026-09-17`) |
| `fig64n.py n` | reads the `6n` squares from the figure under four reading conventions; reports which ones reproduce `Γ_{4,4}` and give a complete datum |
| `g64n.py n [corrected]` | rebuilds the datum from the local permutations printed in Radu's proof; `corrected` fixes the `b_3` misprint; also checks torsion-freeness (no square `(xy)^2`) |
| `xcheck64n.py n [corrected]` | compares the printed local actions with the figure's squares, letter by letter |
| `mktc.py n` | GAP script on the full presentation: `Γ^ab`, and Todd–Coxeter for `Γ/⟨⟨c⟩⟩` over `⟨a_1⟩` and over `1` (closes for n = 2 only) |
| `mkperf.py n` | GAP script on the full presentation: abelian invariants of `Q_c'`, `Q_c = Γ/⟨⟨c⟩⟩` |
| `mkelim.py n MAX cd` | GAP script on the 4-generator Tietze reduction `a_1,a_2,a_3,b_3`: `Γ^ab`, coset enumeration of `⟨a_1⟩` in `Γ/⟨⟨c,d⟩⟩`, and Reidemeister–Schreier for `Q_c'`. `n = 0` gives the n-free group D (enumeration only) |
| `mkwin.py h t MAX` | GAP script for the window groups `W(h,t)`: `a_1,a_2,a_3,b_3`, the `Γ_{4,4}` squares, the two `a_2`-squares, the squares around `b_3,…,b_h` and around `b_{2n},…,b_{2n-t}`. `W(h,t)` surjects onto `Γ_{6,4n}` for every `n ≥ max(h/2,(t+3)/2,2)`. The script enumerates `⟨a_1⟩` in `W/⟨⟨c,d⟩⟩` and runs Reidemeister–Schreier for the index-4 kernel of `W/⟨⟨c⟩⟩` |
| `verwin.py h t n_min n_max` | checks that every abbreviation and relator of `W(h,t)`, read in the letters of `Γ_{6,4n}`, is a square of the figure datum (convention 0), so that the identity on `a_1,a_2,a_3,b_3` is an epimorphism `W(h,t) → Γ_{6,4n}` |
| `relators-64n.txt` | the `6n` square relators for n = 2..12 (convention 0) |
| `run.log` | output of the commands below |

Here `c = [a_1^3,a_2^4]` and `d = [a_2^3,a_1^4]`.

## Reproduce

```sh
export RADU_TEX=/path/to/Lattices3ALL.tex
for n in 2 3 4 5 6 7 8; do
  python3 fig64n.py $n | grep conv
  python3 g64n.py $n; python3 g64n.py $n corrected
  python3 xcheck64n.py $n; python3 xcheck64n.py $n corrected
done
for n in $(seq 2 24); do
  python3 mkelim.py $n 12000000 cd > e$n.g
  timeout 1200 gap -q -o 2g e$n.g < /dev/null | grep -E "n=|Error"
done
python3 mktc.py 2 > t2.g && gap -q -o 2g t2.g < /dev/null
for ht in "3 1" "4 0"; do set -- $ht; python3 mkwin.py $1 $2 100000 > w.g; gap -q -o 2g w.g < /dev/null; done
python3 mkwin.py 5 2 12000000 > w52.g && gap -q -o 2g w52.g < /dev/null
python3 verwin.py 5 2 3 24; python3 verwin.py 5 2 2 2
python3 verwin.py 3 1 2 24; python3 verwin.py 4 0 2 24
```

## Results

**Datum** (n = 2..8):
- `fig64n.py`: convention 0 is the only one that reproduces `Γ_{4,4}`, and it gives a complete datum.
- `g64n.py`: the uncorrected printed permutations admit no valid datum. The corrected ones give
  exactly one, it is torsion-free, and it agrees with the figure (`xcheck64n.py ... corrected`).

**Collapse** (`mkelim.py n 12000000 cd`):
- For every n ∈ {2,…,24}:
  - `Γ^ab = [2,2]`;
  - `[Γ/⟨⟨c,d⟩⟩ : ⟨a_1⟩] = 2`;
  - `[Q_c : Q_c'] = 4`, and `Q_c'` has abelian invariants `[]`, so it is perfect.
- These give `Γ/⟨⟨c,d⟩⟩ ≅ (C_2)^2`; see the proof node for the argument. Times are in `run.log`.

**Uniform collapse** (`mkwin.py 5 2 12000000`, `verwin.py 5 2 3 24`):
- `W(5,2)` has 14 relators, and they are squares of every `Γ_{6,4n}` with n ≥ 3.
- In `W(5,2)/⟨⟨c,d⟩⟩`, `⟨a_1⟩` has index 2 (26 s).
- The index-4 kernel of `W(5,2)/⟨⟨c⟩⟩` is perfect.
- Both properties pass to the quotients `Γ_{6,4n}/⟨⟨c,d⟩⟩` and `Γ_{6,4n}/⟨⟨c⟩⟩`, so the collapse holds for **every** n ≥ 3. With n = 2 computed directly, it holds for all n ≥ 2.
- The larger windows `W(7,3)`, `W(9,5)` and `W(11,7)` also close (`run.log`).

**Uniform perfectness.** `W(3,1)` and `W(4,0)` surject onto every `Γ_{6,4n}` (n ≥ 2). For both,
`W/⟨⟨c⟩⟩` has abelianization `[2,2]`, and its index-4 kernel has abelian invariants `[]`. The
image of that kernel is `Q_c'`, so `Q_c'` is perfect for **every** n ≥ 2.

**n = 2, directly.** `mktc.py 2` enumerates `Γ_{6,8}/⟨⟨c⟩⟩` over the trivial subgroup and gets 4
cosets.

**Negative results.**
- *Full presentation.* Enumeration over `⟨a_1⟩` hits GAP's memory limit at `-o 2g` for n ≥ 6, on
  both `mktc.py` and the `c,d` variant. The Tietze reduction is what makes n ≥ 6 feasible (not recorded in `run.log`).
- *Group D.* `mkelim.py 0 12000000 cd` does not close.
- *Small windows.* For `W(3,1)` and `W(4,0)`, the enumeration of `⟨a_1⟩` in `W/⟨⟨c,d⟩⟩` does not
  close within 10^5 cosets (`run.log`). The window needs the second square of each chain on both
  sides, which is why `W(5,2)` is the smallest one used.

**Trust points.**
- GAP's HLT coset enumerator: a closed table is a proof of the index.
- `MaximalAbelianQuotient`, `IsomorphismFpGroup` (Reidemeister–Schreier) and `AbelianInvariants`.
- The index bookkeeping in `verwin.py` (the proof node states it for general n).
- The correctness of the TeX transcription, which is cross-checked against Radu's printed local
  actions.
