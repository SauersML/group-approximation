# Positive-cone certificates for Radu's lattices (2026-09-17)

Supports `research/radu-simple-six-six-lattices-are-not-left-orderable.md`.

## Files
- `bmw.py`: normal-form multiplication in a (d1,d2)-group (BMW group). Contains `RADU_44` (Radu's `Gamma_{4,4}`) and `RADU_66` (`Gamma_{6,6,2}`), both transcribed from arXiv:1712.01091 and compared with its TeX source by regex. `test_bmw.py` holds the unit tests.
- `lo_sat.py`, `lo_search.py`: build the positive-cone CNF on a ball, solve it with CaDiCaL (pysat), and shrink the result to a deletion-minimal core.
- `ab_search.py L SHORT MODE [OUT]`: the same search restricted to ball elements with trivial image in `Gamma_{4,4}^ab` (`MODE=derived`).
- `ncl_search.py GROUP R LEVELS [OUT]`: searches the normal closure of `[a1^3,a2^4]` and `[a2^3,a1^4]`. It found nothing (negative result).
- `verify_certificate.py GROUP FILE MODE`: an independent checker. It rewrites `p q r^-1` to the empty word with relator moves only, checks that every element is nontrivial, and runs a complete DPLL.
- `derived_check.py radu44 FILE`: checks, with exact integer arithmetic, that every word in a certificate lies in `[Gamma_{4,4}, Gamma_{4,4}]`.
- `certificate-gamma44-derived-L6.txt`: 124 triples, in `Gamma_{4,4}'`.
- `certificate-gamma44-kernel-L6.txt`: 70 triples, in `Gamma_{4,4}^+`.
- `certificate-gamma662-kernel-L4.txt`: 169 triples, in `Gamma_{6,6,2}^+`.
- `run.log`: output of every command below.

## Reproduce
Each command runs single-threaded in seconds to minutes and needs `pysat`.

```
python3 test_bmw.py
python3 lo_search.py radu44 4 kernel 2
python3 lo_search.py radu44 6 kernel 2 certificate-gamma44-kernel-L6.txt
python3 lo_search.py radu66 4 kernel 2 certificate-gamma662-kernel-L4.txt
python3 ab_search.py 6 2 derived
python3 ab_search.py 6 4 derived certificate-gamma44-derived-L6.txt
python3 verify_certificate.py radu44 certificate-gamma44-kernel-L6.txt kernel
python3 verify_certificate.py radu66 certificate-gamma662-kernel-L4.txt kernel
python3 verify_certificate.py radu44 certificate-gamma44-derived-L6.txt kernel
python3 derived_check.py radu44 certificate-gamma44-derived-L6.txt
python3 ncl_search.py radu44 2 2
```

For the exact argument order, see `run.log` and the usage string in each script.

## Results
| group | ball | result | certificate |
|---|---|---|---|
| `Gamma_{4,4}^+` | radius 4 | SAT | none |
| `Gamma_{4,4}^+` | radius 6 | UNSAT | 70 triples, VALID (15 DPLL nodes) |
| `Gamma_{6,6,2}^+` | radius 4 | UNSAT | 169 triples, VALID (359 nodes) |
| `Gamma_{4,4}'` | radius 6, short factors of length 2 or less | SAT | none |
| `Gamma_{4,4}'` | radius 6, short factors of length 4 or less | UNSAT | 124 triples, VALID (71 nodes); all 372 words lie in `[G,G]` |
| normal closure of `[a1^3,a2^4]` and `[a2^3,a1^4]` | conjugators of radius 2 or less, products of two | SAT (19492 elements) | none |

Negative controls for `derived_check.py`:
- `a1 b2` is reported outside `[G,G]`.
- 159 of the 210 words in the `Gamma^+` certificate are reported outside `[G,G]`.
