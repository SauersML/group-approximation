# 40_40#281: the invariant-subtree automaton group is a Möbius group over F_3((s))

Claim: `research/bmw-40-40-281-is-irreducible.md`. Proof: `research/bmw-40-40-281-irreducible-mobius-proof.md`.

All scripts run from this directory; python3 (sympy for `mobius281.py`), GAP 4 (`gap -q < /dev/null`).

## Proof-relevant

| file | what it does |
|---|---|
| `aut.py` | the automata `K` (`AUT['281']`, also 332/193 V/H), level permutations |
| `checkaut.py`, `checkaut.log` | `AUT['281']` equals `selfrep.build` of census_40_40 #281 on both sides (reads `../bmw-census-left-orders-2026-09-17/`) |
| `mobius281.py`, `mobius281.log` | exact check of the 12 intertwining identities `A_g t_x = t_{out} A_{sec}` and `T^2 = 1`, two negative controls, orders of `τa_2` on levels 1–9 |

## Discovery and cross-checks (not needed for the proof)

| file | what it does |
|---|---|
| `ser.py` | power series mod `s^m`; `is_mob` recognises a permutation of `O/s^m` as a semilinear Möbius map with `γ ∈ sO` |
| `rho2.py`, `rho2.log` | search over coordinate ansätze; 162 solutions on levels 2–4 (first listed is the one used) |
| `rho3.py`, `rho3.log` | the chosen coordinates on levels 2–8: Möbius data of the four generators (`T`: `α=−1`, `β=1+s+s²+…`, `γ=−s−s²−…`) |
| `mkgap.py`, `g281_N.g` | GAP generators of `K` on level `N` |
| `chain.g`, `run_chain.g`, `chain.log` | section chain `G_{k+1} = φ_0(Stab_{G_k}(0))`: `|G_k|` on level `m` is `4·3^{max(3m−2−k, 2m−1)}`, strictly decreasing, `|K_7| = 4·3^19` |
| `l2test.g`, `l2test.log` | w3-107's `L_2` is **not** self-replicating at 0: index 3 modulo level 5, generators 4, 6, 7 outside |
| `mobgen.py`, `mob2..4.g` | the semilinear Iwahori Möbius group `M_m` on `O/s^m` |
| `compare.g`, `compare.log` | `M_m` vs `K_m`, `m = 2,3,4`: same order, derived and lower central series, centre, exponent, class data |
| `iso3.g`, `iso3.log` | a tree-compatible permutation isomorphism `M_3 ≅ K_3` |
| `ords.py`, `ord1.py`, `ord1.log` | element orders on deep levels (order 81 on level 14) |
