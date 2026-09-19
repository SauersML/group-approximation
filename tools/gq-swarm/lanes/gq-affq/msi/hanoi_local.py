#!/usr/bin/env python3
"""Two-level design test for a binary (height-2) Hanoi machine in 3V.

Three pegs = three stacks (one per Cantor coordinate).  The optimal Tower of Hanoi solution
alternates: odd steps move disk 1 (cyclically, fixed direction); even steps make the unique
legal move between the two other pegs.  Moves are pop/push on stack tops (bounded).  The
question: is the even-step move a function of BOUNDED local data at the three tops?

Local data offered at an even step (r = peg of disk 1, pegs a = r+1, b = r+2 mod 3):
  parity of top(a), parity of top(b)  (None if empty),
  mark(a), mark(b): whether that top is the disk moved at the previous even step,
  depth-2 parities (second disk on each stack).
We record (local data) -> correct move over the full optimal solution for several n, and report
conflicts (the same data needing different moves).  Zero conflicts = the move is locally
decidable from that data (on genuine Hanoi configurations)."""
import sys, collections


def solve(n):
    moves = []

    def rec(k, src, dst, via):
        if k == 0:
            return
        rec(k - 1, src, via, dst)
        moves.append((k, src, dst))
        rec(k - 1, via, dst, src)
    rec(n, 0, 2, 1)
    return moves


def main():
    for feats in ('parity', 'parity+mark', 'parity+mark+depth2'):
        table = collections.defaultdict(set)
        total = 0
        for n in range(3, 15):
            pegs = [list(range(n, 0, -1)), [], []]  # bottom ... top
            last_even_disk = None
            for i, (k, s, d) in enumerate(solve(n)):
                if k != 1:
                    r = next(p for p in range(3) if pegs[p] and pegs[p][-1] == 1)
                    a, b = (r + 1) % 3, (r + 2) % 3

                    def top(p, depth=1):
                        return pegs[p][-depth] if len(pegs[p]) >= depth else None

                    def par(x):
                        return None if x is None else x % 2

                    key = [n % 2, par(top(a)), par(top(b))]
                    if 'mark' in feats:
                        key += [top(a) == last_even_disk, top(b) == last_even_disk]
                    if 'depth2' in feats:
                        key += [par(top(a, 2)), par(top(b, 2))]
                    move = 'a->b' if (s, d) == (a, b) else ('b->a' if (s, d) == (b, a) else '?')
                    # also depend on n's parity? record separately: the infinite machine has none
                    table[tuple(key)].add(move)
                    total += 1
                    last_even_disk = k
                x = pegs[s].pop()
                assert x == k
                pegs[d].append(x)
        conflicts = {k: v for k, v in table.items() if len(v) > 1}
        print(f'{feats:22s} even-steps {total}  distinct keys {len(table)}  conflicting keys {len(conflicts)}')
        for k, v in sorted(conflicts.items(), key=str)[:6]:
            print('   conflict', k, sorted(v))


if __name__ == '__main__':
    main()
