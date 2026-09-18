#!/usr/bin/env python3
"""SMART on conveyor belts: reversibility, cycle periods, and the belt-confinement bound.

Context: research/brin-thompson-nv-integrated-local-walls-bounded-on-distortion-element.md.

Callard--Salo (arXiv:2208.00685, Sec. 3.1) run a Turing machine M on the full shift by
"conveyor belts": x and f_M(x) have the same belt decomposition, and f_M acts on each belt
(a word w with one head) as M on the cyclic tape of length 2|w|. So every point whose head
belt is finite lies in a finite f-invariant family of cylinders, and the head never leaves the
belt. This script checks, for the SMART machine transcribed from the tikz diagram in
distortion-1-smart.tex:

  1. the transition table is complete and reversible;
  2. on cyclic tapes of length c = 2*ell, T_M is a permutation of Q x Z_c x Gamma^c; the script
     reports the maximal and mean cycle length (the period P_ell of f on belts of length ell);
  3. the tail bound: under a Bernoulli measure where a cell carries conveyor bit +1 (or -1)
     with probability at most p < 1, the belt length L satisfies P(L >= ell) <= 2 ell p^(ell-1),
     hence sum_ell (ell+1) P(L = ell) < infinity. The script prints this sum for the uniform
     measure on Callard--Salo's alphabet as a numerical sanity check.

Usage: python3 smart_belt_periods.py [max_c]   (default max_c = 10, even lengths only)
"""
import sys
from math import gcd

# States: (shape, dir, phase) with shape in {F (filled), H (hollow)}, dir in {+1, -1},
# phase in {1, 2}.  Phase 2 states only move (by dir) and enter phase 1.
# Phase 1 states read a symbol, write a symbol and enter a phase-2 state.
STATES = [(s, d, p) for s in "FH" for d in (+1, -1) for p in (1, 2)]
GAMMA = (0, 1, 2)

# Symbol transitions (state, read) -> (write, new_state), transcribed from the diagram:
#  |>1 (F,+1,1): 0|1 -> <|2 (F,-1,2);  1|1, 2|2 -> <|hollow 2 (H,-1,2)
#  <|1 (F,-1,1): 0|1 -> |>2 (F,+1,2);  1|1, 2|2 -> hollow |> 2 (H,+1,2)
#  hollow |>1 (H,+1,1): 0|2, 1|0 -> |>2 (F,+1,2);  2|0 -> hollow <| 2 (H,-1,2)
#  hollow <|1 (H,-1,1): 0|2, 1|0 -> <|2 (F,-1,2);  2|0 -> hollow |> 2 (H,+1,2)
SYM = {
    (("F", +1, 1), 0): (1, ("F", -1, 2)),
    (("F", +1, 1), 1): (1, ("H", -1, 2)),
    (("F", +1, 1), 2): (2, ("H", -1, 2)),
    (("F", -1, 1), 0): (1, ("F", +1, 2)),
    (("F", -1, 1), 1): (1, ("H", +1, 2)),
    (("F", -1, 1), 2): (2, ("H", +1, 2)),
    (("H", +1, 1), 0): (2, ("F", +1, 2)),
    (("H", +1, 1), 1): (0, ("F", +1, 2)),
    (("H", +1, 1), 2): (0, ("H", -1, 2)),
    (("H", -1, 1), 0): (2, ("F", -1, 2)),
    (("H", -1, 1), 1): (0, ("F", -1, 2)),
    (("H", -1, 1), 2): (0, ("H", +1, 2)),
}


def check_reversible():
    # Complete: every phase-1 (state, symbol) has exactly one transition (true by construction).
    for q in STATES:
        if q[2] == 1:
            for a in GAMMA:
                assert (q, a) in SYM
    # Reverse deterministic: (new_state, written symbol) determines (state, read symbol).
    seen = {}
    for key, val in SYM.items():
        assert val not in seen, ("not reversible", key, seen.get(val))
        seen[val] = key
    # Every phase-2 state and symbol is hit exactly once, so the symbol step is a bijection
    # from phase-1 x Gamma onto phase-2 x Gamma; moves are bijections phase-2 -> phase-1.
    targets = {(b, q) for (b, q) in SYM.values()}
    assert len(targets) == 4 * 3
    return True


def step(q, pos, tape, c):
    s, d, p = q
    if p == 2:
        return (s, d, 1), (pos + d) % c, tape
    b, q2 = SYM[(q, tape[pos])]
    t = list(tape)
    t[pos] = b
    return q2, pos, tuple(t)


def periods(c):
    """Cycle lengths of T_M on the cyclic tape of length c."""
    from itertools import product
    idx = {}
    configs = []
    for q in STATES:
        for pos in range(c):
            for tape in product(GAMMA, repeat=c):
                idx[(q, pos, tape)] = len(configs)
                configs.append((q, pos, tape))
    n = len(configs)
    seen = bytearray(n)
    cycles = []
    for i in range(n):
        if seen[i]:
            continue
        j, length = i, 0
        while not seen[j]:
            seen[j] = 1
            length += 1
            j = idx[step(*configs[j], c)]
        assert j == i, "T_M not a permutation"
        cycles.append(length)
    return n, cycles


def lcm_list(xs):
    out = 1
    for x in xs:
        out = out * x // gcd(out, x)
    return out


def main():
    max_c = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    print("reversible:", check_reversible())
    print("c = 2*ell | configs | #cycles | max cycle | mean cycle (config-weighted) | log2 lcm")
    for c in range(2, max_c + 1, 2):
        n, cyc = periods(c)
        wmean = sum(x * x for x in cyc) / n
        print(f"{c:3d} | {n:9d} | {len(cyc):7d} | {max(cyc):9d} | {wmean:12.1f} | "
              f"{lcm_list(cyc).bit_length()}")
    # Tail sum for the belt length in the RTM(18, 96) model (Callard--Salo, proof of the
    # Turing-machine theorem): tape cells range over Gamma^2 x {+1,-1} (18 symbols), one head at
    # the origin.  Under the uniform Bernoulli measure a cell is a +1 cell with probability 1/2.
    # The head's belt is the left run of +1 cells plus the right run of -1 cells.
    p = 0.5
    tail = sum((a + b + 2) * (1 - p) ** 2 * p ** (a + b) for a in range(200) for b in range(200))
    print(f"RTM(18,96) uniform measure: p(+1 cell) = {p}; E[belt length + 1] = {tail:.5f}")


if __name__ == "__main__":
    main()
