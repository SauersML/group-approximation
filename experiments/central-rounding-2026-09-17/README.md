# central-rounding-2026-09-17

`check_rounding.py` numerically checks Step 2 (the rounding inequality) of
`research/central-power-quotient-gaps-converge-to-the-extension-gap-proof.md`
on random unitary triples, using the torus-knot relators of `T̄`
(`a^4 = z`, `b^3 = z`, `(ba)^5 = z^3`, `[z,a]`, `[z,b]`; `L = 3`).

Run `python3 check_rounding.py` (numpy, scipy). Expected output:
`OK: 300 trials; minimal slack in defect bound = 0.10747`.

It is a sanity check of an elementary inequality, not evidence about any group.
