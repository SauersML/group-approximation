"""Fano charging constant c7 for Lemma F7 (gstar-star-linearity-is-stable-near-full-value).

Quotient R/W0 = F_2^3. Points x (the (l-1)-spaces W between W0 and R), lines T
(the l-spaces), each T labelled by (colour, beta) where colour = F(T)|_W0 and beta =
restriction of F(T) to the 2-dim line T cap E3 (4 choices). Only the partition of the
7 lines into colour classes matters, so mode "all" enumerates all Bell(7)=877 set
partitions (restricted growth strings) times 4^7 betas: every coloured labelling.
Point labels are chosen by plurality (optimal for unsat, and a full star is full for
any point label only if it is full for the plurality label). A star x is twisted-full
if its 3 edges are satisfied and the 3 line labels have no common linear extension.
Prints max #twisted / #unsat and asserts unsat = 0 implies twisted = 0.
Usage: python3 fano_twist.py [C | all]
"""
import itertools
import sys
from fractions import Fraction

pts = list(range(1, 8))


def dot(a, b):
    return bin(a & b).count("1") & 1


lines = sorted({tuple(sorted((a, b, a ^ b))) for a in pts for b in pts if a != b})
restr = []  # 4 representative vectors per line (distinct restrictions)
for L in lines:
    seen = {}
    for v in range(8):
        seen.setdefault(tuple(dot(v, x) for x in L), v)
    restr.append(list(seen.values()))
through = {x: [i for i, L in enumerate(lines) if x in L] for x in pts}
# bit[i][b][x] = value at point x of beta option b on line i
bit = [[{x: dot(restr[i][b], x) for x in lines[i]} for b in range(4)] for i in range(7)]
# ext[x][(b1,b2,b3)] = the three betas on the lines through x extend to F_2^3
ext = {}
for x in pts:
    ls = through[x]
    for bs in itertools.product(range(4), repeat=3):
        ext[x, bs] = any(all(dot(g, y) == bit[i][b][y] for i, b in zip(ls, bs) for y in lines[i])
                         for g in range(8))


def score(col, bet):
    unsat = tw = 0
    for x in pts:
        ls = through[x]
        votes = [(col[i], bit[i][bet[i]][x]) for i in ls]
        best = max(votes.count(v) for v in votes)
        unsat += 3 - best
        if best == 3 and not ext[x, tuple(bet[i] for i in ls)]:
            tw += 1
    return tw, unsat


def rgs(n):
    """restricted growth strings = set partitions of n elements"""
    def rec(pre, m):
        if len(pre) == n:
            yield tuple(pre)
            return
        for c in range(m + 2):
            yield from rec(pre + [c], max(m, c))
    yield from rec([0], 0)


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else "1"
    if arg == "all":
        cols = list(rgs(7))
    else:
        C = int(arg)
        cols = [c for c in rgs(7) if max(c) < C]
    best, where, npart = Fraction(0), None, 0
    for col in cols:
        npart += 1
        for bet in itertools.product(range(4), repeat=7):
            tw, un = score(col, bet)
            assert un or not tw, "fully satisfied Fano configuration with a twist"
            if un and Fraction(tw, un) > best:
                best, where = Fraction(tw, un), (tw, un, col)
    print(f"partitions={npart}: c7 = {best} attained at (twisted, unsat, colouring) = {where}")
    return best


if __name__ == "__main__":
    main()
