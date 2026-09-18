# BS(1,2): one design pass on the two-head / even-arity route (lane gq-affq, 2026-09-18)

**Scope** (coordinator): one design pass. The target is a reversible machine in `2V` or `3V`
whose second head (or coordinate) carries the return-turn information that the one-head
Jacobsthal scheme lacks. Candidates were to be filtered by the eigenvalue test first
(`smart-induced-map-alternates-head-direction`: a height-2 renormalization needs `i ∈ E(S)`), then
put through induce → factor → renormalize. **Outcome: no candidate reached the filter.** Every
design either left `kV` or needed unbounded control information. What follows is the design
analysis and the obstruction met.

## 1. Two heads on one tape are not elements of `kV`

An element of `kV` is locally a prefix replacement at the `k` coordinate tops. A configuration
therefore has exactly `k` access points. A two-head machine on one bi-infinite tape has three
tape segments: left of head 1, between the heads, and right of head 2. The middle segment is
finite and unbounded in length, and it is not a Cantor coordinate. Coding it into a coordinate
puts one of its ends at unbounded depth, so the head at that end is not accessible. **So the
second head must live on its own coordinate.** It cannot mark a position on head 1's tape;
anything it contributes is memory.

## 2. Second coordinate as a displacement stack

Give head 1 a tape (coordinates 1 and 2) and let coordinate 3 be a stack. Push a symbol on each
step away from the current anchor and pop one on each step back. Then "one cell before the
anchor", the Jacobsthal return-turn condition that the one-head scheme cannot see, becomes a
depth-2 test at the top of the stack. That test is bounded.

**Where it fails: nested anchors.** Moves nest, so the stack must hold one counter per active
level: `[child count] sep [parent count] sep …`.
- A return ends at its anchor, with child count `0`, so its separator can be popped at once.
- A crossing ends at the far end of its domain. The parent's count must then absorb the child's,
  which means deleting the separator **beneath** the child's `L` symbols, at depth `L`. The
  alternatives are an `L`-step walk or unbounded lookahead.

So the displacement stack turns the turn test into a bounded one but moves the unbounded cost
into merging counters. This is the same linear walk that gq-nv-obstruct's one-head search
finds.

## 3. Three stacks: Tower of Hanoi (exact doubling, but a non-local decision)

Three pegs are three stacks, so this is `3V`. The optimal Hanoi solution alternates two kinds of
move:
- an odd step moves disk 1 cyclically;
- an even step makes the unique legal move between the other two pegs.

Every move is a pop and a push at stack tops, so it is bounded. The recursion
`f(n) = 2f(n-1) + 1` gives `f(n) + 1 = 2^n` **exactly**, with no walk: the hierarchy is genuinely
binary, and odd branching is avoided because no head crosses a domain. The obstruction is the
**even-step decision**. The legal move places the smaller top on the larger, which is an order
comparison of unbounded labels. The MSI test in §5 asked whether bounded local data at the tops
determines the move, over the full optimal solutions for `n = 3, …, 15` (16,368 even steps).

| local data at the two relevant tops | conflicting keys |
|---|---|
| parities | 2 |
| parities + parity of `n` | 2 |
| + "moved at the previous even step" mark | 2 |
| + depth-2 parities | 8 |
| size mod `M`, `M = 2, 3, 4, 5, 6, 8, 12` (+ `n mod 2` + mark) | 2, 18, 8, 29, 18, 29, 16 |
| size mod 16 | 0, trivially: every disk has size ≤ 15, so the label is the exact size |

The conflicts sit exactly in the mixed-parity case where neither top moved last. There the correct
move depends on which top is smaller. This is evidence, not proof, that **no bounded labelling
decides the Hanoi move**.

## 4. The common obstruction (conjecture)

In all three designs, and in gq-nv-obstruct's one-head searches
(`crossing-move-hierarchies-have-odd-branching`,
`research/artifacts/gq-gq-nv-obstruct-binary-smart-search.md`), a **binary** hierarchy needs
control information that grows with the level. That information is the distance to a turning
point, a merged count, or an order comparison. Inside `kV` it can be paid for only as unbounded
lookahead, which is not allowed, or as a level-linear walk, which destroys exact doubling, so the
first-return tool no longer applies. SMART escapes this only because odd branching needs no
turning decision.

**Conjecture:** no element of any `kV` built this way has a height-2 renormalization. Proving it
would need an invariant that turns "level-dependent control" into a contradiction with
brick-locality. None is offered here.

## 5. Scripts (MSI `/projects/standard/hsiehph/sauer354/gqsrc/gq-affq/`)

`hanoi_local.py`: bounded-feature decidability of the Hanoi even move (parity, `n mod 2`, mark,
depth-2).

```python
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
```

`hanoi_mod.py`: size-mod-`M` labels.

```python
#!/usr/bin/env python3
"""Hanoi even-step decidability from bounded labels: label = disk size mod M at each top
(plus n mod 2 and the last-moved mark).  Conflicts = same bounded data, different correct move."""
import collections, sys
sys.setrecursionlimit(10000)


def solve(n):
    moves = []

    def rec(k, s, d, v):
        if k:
            rec(k - 1, s, v, d); moves.append((k, s, d)); rec(k - 1, v, d, s)
    rec(n, 0, 2, 1)
    return moves


for M in (2, 3, 4, 5, 6, 8, 12, 16):
    table = collections.defaultdict(set)
    for n in range(3, 16):
        pegs = [list(range(n, 0, -1)), [], []]
        last = None
        for k, s, d in solve(n):
            if k != 1:
                r = next(p for p in range(3) if pegs[p] and pegs[p][-1] == 1)
                a, b = (r + 1) % 3, (r + 2) % 3
                ta = pegs[a][-1] if pegs[a] else None
                tb = pegs[b][-1] if pegs[b] else None
                key = (n % 2, None if ta is None else ta % M, None if tb is None else tb % M,
                       ta == last, tb == last)
                table[key].add('a->b' if (s, d) == (a, b) else 'b->a')
                last = k
            pegs[d].append(pegs[s].pop())
    conf = sum(1 for v in table.values() if len(v) > 1)
    print(f'labels size mod {M:2d}: keys {len(table):4d}  conflicting {conf}')
```
