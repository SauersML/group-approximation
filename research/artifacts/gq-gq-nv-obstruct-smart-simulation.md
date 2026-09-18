# SMART induced on genuine level-0 moves: desubstitution and local-phase computation (lane gq-nv-obstruct, 2026-09-17)

Supports `smart-level-zero-return-map-factors-onto-3-adic-odometer`, which is still under review. Run on MSI (acn node, single core), with `module load python3` and `python3 smart_induced_odometer.py 177147 7`, in `/projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct/`. Script md5 `a6d2f623bb432404d86b681b73c818bf`. The run took well under 10 minutes and left no processes. Nothing was run locally.

## Output (run1.out, verbatim)

```
steps per run 177147 kmax 7
zero-b1   Ytimes   59049  max return gap 6  desub depth 8  offsets per level [[0], [0], [0], [0], [0], [0], [0], [0], [0]]
zero-p1   Ytimes   59049  max return gap 6  desub depth 8  offsets per level [[0], [0], [0], [0], [0], [0], [0], [0], [0]]
random-0  Ytimes   59049  max return gap 6  desub depth 8  offsets per level [[0], [1], [1], [0], [0], [0], [2], [2], [0]]
random-1  Ytimes   59050  max return gap 6  desub depth 8  offsets per level [[1], [1], [2], [0], [2], [0], [0], [0], [2]]
random-2  Ytimes   59049  max return gap 6  desub depth 8  offsets per level [[2], [2], [0], [2], [0], [2], [0], [1], [1]]
random-3  Ytimes   59050  max return gap 6  desub depth 8  offsets per level [[0], [1], [2], [0], [0], [1], [2], [0], [2]]
sparse    Ytimes   59049  max return gap 6  desub depth 8  offsets per level [[0], [0], [0], [0], [0], [0], [0], [0], [0]]
k=1  radius 3  distinct windows 5832  conflicts 0
k=2  radius 4  distinct windows 51753  conflicts 0
k=3  radius 5  distinct windows 271606  conflicts 0
k=4  radius 6  distinct windows 390654  conflicts 0
k=5  radius 7  distinct windows 408690  conflicts 0
k=6  radius 8  distinct windows 412135  conflicts 0
k=7  radius 9  distinct windows 409414  conflicts 0
SMART_INDUCED_ODOMETER_DONE
```

## Reading

- **T1, bounded return.** The maximal gap between consecutive `Y`-times is 6 on every run. This matches gq-affq's `r_Y <= 6` (`smart-induced-on-genuine-moves-has-exact-tripling`).
- **T2, recognizability.** On every start, the `Y`-letter word desubstitutes under `b→bdp, d→dbq, p→bqp, q→dpq` with **exactly one** working offset at each of 8 levels, down to words of length 12 or more. The starts are: the all-zero tape with `b1` or `p1`, four uniform random tapes, and one sparse random tape. The 8 levels are all the word length allows.
- **T3, local phase.** Fix the phases by T2. The pair (state, cells within radius `k+2` of the head) then determines `pos_k`, the number of level-0 moves before the head in its level-`k` move, with **0 conflicts** pooled over all 7 runs, for `k = 1..7`.
  - For `k <= 3` the windows repeat heavily (5,832 distinct windows at `k = 1` against about 413k samples), so the test has teeth there.
  - For `k >= 4` almost every window is new, so the test is weak there. The proof in `gq-gq-nv-obstruct-smart-odometer.md` §2–3 covers all `k`.

## Script (verbatim)

```python
#!/usr/bin/env python3
"""SMART induced on genuine level-0 moves: desubstitution and local phase test.

Lane gq-nv-obstruct, 2026-09-17. Runs on MSI only (single core, a few minutes).

SMART (Callard--Salo arXiv:2208.00685v3, distortion-1-smart.tex, l. 2-35), Kari--Ollinger model:
  moves:   b2 -> b1 (+1), d2 -> d1 (-1), p2 -> p1 (+1), q2 -> q1 (-1)
  symbols: b1: 0|1->d2, 1|1->q2, 2|2->q2     d1: 0|1->b2, 1|1->p2, 2|2->p2
           p1: 0|2->b2, 1|0->b2, 2|0->q2     q1: 0|2->d2, 1|0->d2, 2|0->p2
Y (gq-affq, eddfd3d4b): phase-2 configurations that are genuine level-0 moves:
  b2 or d2 on a nonzero cell; p2 with nonzero right neighbour; q2 with nonzero left neighbour.
Claimed (smart-level-zero-return-map-factors-onto-3-adic-odometer): the sequence of move letters along
any orbit, read only at Y-times, is a factor of a fixed point of the constant-length-3 substitution
  b -> bdp, d -> dbq, p -> bqp, q -> dpq,
and the level-k phase is a function of the (k+2)-neighbourhood of the head.
Tests, for several start configurations (Z-tapes):
  T1 return times to Y are bounded;
  T2 the Y-letter word desubstitutes uniquely (exactly one offset per level works) to depth K;
  T3 with the phases fixed by T2, the window of radius k+2 (state + cells) determines pos_k, the
     level-0 count inside the current level-k move, pooled over all runs (a function, no conflicts).
"""
import random
import sys

MOVE = {('b', 2): ('b', 1, +1), ('d', 2): ('d', 1, -1), ('p', 2): ('p', 1, +1), ('q', 2): ('q', 1, -1)}
SYM = {
    ('b', 0): (1, 'd'), ('b', 1): (1, 'q'), ('b', 2): (2, 'q'),
    ('d', 0): (1, 'b'), ('d', 1): (1, 'p'), ('d', 2): (2, 'p'),
    ('p', 0): (2, 'b'), ('p', 1): (0, 'b'), ('p', 2): (0, 'q'),
    ('q', 0): (2, 'd'), ('q', 1): (0, 'd'), ('q', 2): (0, 'p'),
}
SIGMA = {'b': 'bdp', 'd': 'dbq', 'p': 'bqp', 'q': 'dpq'}
INV = {v: k for k, v in SIGMA.items()}


def y_letter(tape, h, s):
    """Move letter if the configuration is in Y, else None."""
    a, ph = s
    if ph != 2:
        return None
    if a in 'bd':
        return a if tape[h] != 0 else None
    if a == 'p':
        return a if tape[h + 1] != 0 else None
    return a if tape[h - 1] != 0 else None


def run(tape, h, s, nsteps, rmax):
    """Simulate; return list of (letter, window_by_radius_dict_builder_args) at Y-times."""
    ys = []
    last = None
    maxgap = 0
    for t in range(nsteps):
        if h - rmax - 2 < 0 or h + rmax + 2 >= len(tape):
            break
        L = y_letter(tape, h, s)
        if L is not None:
            if last is not None:
                maxgap = max(maxgap, t - last)
            last = t
            ys.append((L, s, h, tuple(tape[h - rmax:h + rmax + 1])))
        a, ph = s
        if ph == 2:
            a2, ph2, dh = MOVE[s]
            s = (a2, ph2)
            h += dh
        else:
            b, a2 = SYM[(a, tape[h])]
            tape[h] = b
            s = (a2, 2)
    return ys, maxgap


def desubstitute(word, depth):
    """Return list of (offset, preimage) per level, and uniqueness flags."""
    levels = []
    w = word
    for lev in range(depth):
        ok = []
        for o in range(3):
            blocks = [w[i:i + 3] for i in range(o, len(w) - 2, 3)]
            if blocks and all(bl in INV for bl in blocks):
                ok.append(o)
        if len(ok) != 1 or len(w) < 12:
            levels.append((ok, None))
            break
        o = ok[0]
        pre = ''.join(INV[w[i:i + 3]] for i in range(o, len(w) - 2, 3))
        levels.append((ok, pre))
        w = pre
    return levels


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3 ** 11
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    rmax = kmax + 2
    random.seed(20260917)
    starts = []
    size = 2 * n + 4 * rmax + 10
    # 1. all-zero Z-tape, head b1 (C_b on Z)
    starts.append(('zero-b1', [0] * size, size // 2, ('b', 1)))
    # 2. all-zero Z-tape, head p1
    starts.append(('zero-p1', [0] * size, size // 2, ('p', 1)))
    # 3-6. uniform random tapes, random states
    for i in range(4):
        tape = [random.randrange(3) for _ in range(size)]
        s = (random.choice('bdpq'), random.choice((1, 2)))
        starts.append(('random-%d' % i, tape, size // 2, s))
    # 7. sparse random tape (P(nonzero) = 0.05): long zero blocks
    tape = [random.randrange(1, 3) if random.random() < 0.05 else 0 for _ in range(size)]
    starts.append(('sparse', tape, size // 2, ('d', 2)))

    pooled = [dict() for _ in range(kmax + 1)]
    conflicts = [0] * (kmax + 1)
    print('steps per run', n, 'kmax', kmax)
    for name, tape, h, s in starts:
        ys, gap = run(tape, h, s, n, rmax)
        word = ''.join(L for L, _, _, _ in ys)
        levels = desubstitute(word, kmax + 3)
        offs = [lv[0] for lv in levels]
        depth_ok = sum(1 for lv in levels if len(lv[0]) == 1 and lv[1] is not None)
        print('%-9s Ytimes %7d  max return gap %d  desub depth %d  offsets per level %s' % (
            name, len(ys), gap, depth_ok, offs))
        # absolute offset of level-k blocks in level-0 positions: o_k = sum_{i<k} off_i * 3^i
        base = 0
        absoff = [0]
        for i, lv in enumerate(levels):
            if len(lv[0]) != 1 or lv[1] is None:
                break
            base += lv[0][0] * 3 ** i
            absoff.append(base)
        for k in range(1, min(kmax, len(absoff) - 1) + 1):
            o = absoff[k]
            r = k + 2
            for tau, (L, st, hh, win) in enumerate(ys):
                if tau < o:
                    continue
                pos = (tau - o) % 3 ** k
                key = (st, win[rmax - r:rmax + r + 1])
                prev = pooled[k].get(key)
                if prev is None:
                    pooled[k][key] = pos
                elif prev != pos:
                    conflicts[k] += 1
    for k in range(1, kmax + 1):
        print('k=%d  radius %d  distinct windows %d  conflicts %d' % (k, k + 2, len(pooled[k]), conflicts[k]))
    print('SMART_INDUCED_ODOMETER_DONE')


if __name__ == '__main__':
    main()
```
