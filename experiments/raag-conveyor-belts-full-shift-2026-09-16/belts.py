#!/usr/bin/env python3
"""Exact checks of the simplified conveyor-belt embedding A_Gamma -> [[Sigma^Z]].

Construction (research/artifacts/raags-in-2v-via-full-shift-full-group-2026-09-16.md, Part B):
  alphabet: letters T(u)=2u, B(u)=2u+1 for vertices u in 0..N-1, '#'=2N, junk=2N+1.
  A u-block at i: x_i = T(u), x_{i+1} = B(u).  A u-belt is a maximal run of
  consecutive u-blocks at i, i+2, ..., i+2L-2, with cells T_1..T_L (T letters)
  and B_1..B_L (B letters).  If the next block (at i+2L) has type w not adjacent
  to u, the cell B_L is relocated onto that w-block's T letter.
  f_u moves the head around T_1 -> ... -> T_L -> B_L -> ... -> B_1 -> T_1 and
  fixes every other position.  Its cocycle reads x_[-4,3].

Checks:
  1. bijectivity of the head map p_x on every periodic configuration of small
     period (exhaustive), and on random long periodic configurations;
  2. p^{f_u} and p^{f_w} commute on those configurations when {u,w} is an edge;
  3. faithfulness: for every reduced syllable word (bounded length/exponent)
     the greedy chain configuration displaces the head, and on random
     unreduced words the head map on the chain configuration of the reduced
     form is consistent with the RAAG normal form.
All arithmetic is exact (integers).  Single-threaded; run with `timeout 600`.
"""
import itertools
import random
import sys


class Belts:
    def __init__(self, n, edges):
        self.n = n
        self.adj = [[False] * n for _ in range(n)]
        for a, b in edges:
            self.adj[a][b] = self.adj[b][a] = True
        self.hash = 2 * n
        self.junk = 2 * n + 1
        self.alphabet = list(range(2 * n + 2))

    def nonadj(self, u, w):
        return u != w and not self.adj[u][w]

    def btype(self, x, i, per):
        a = x[i % per]
        b = x[(i + 1) % per]
        # block of type a//2 iff a is a T letter and b the matching B letter
        return a // 2 if (a < 2 * self.n and a % 2 == 0 and b == a + 1) else None

    def is_block(self, x, i, u, per):
        return x[i % per] == 2 * u and x[(i + 1) % per] == 2 * u + 1

    def cocycle(self, u, x, i, per):
        """Cocycle of f_u at the shifted configuration sigma^i(x); x periodic, period per."""
        if self.n <= 0:
            return 0
        xi = x[i % per]
        if xi >= 2 * self.n:
            return 0
        if self.is_block(x, i, u, per):  # head on T_k
            if self.is_block(x, i + 2, u, per):
                return 2  # T_k -> T_{k+1}
            t = self.btype(x, i + 2, per)
            if t is not None and self.nonadj(u, t):
                return 2  # T_L -> relocated B_L
            return 1  # T_L -> B_L (unrelocated)
        if xi == 2 * u + 1 and x[(i - 1) % per] == 2 * u:  # head on a B letter of a u-block
            t = self.btype(x, i + 1, per)
            if t is not None and self.nonadj(u, t):
                return 0  # this B_L was relocated: not a cell
            if self.is_block(x, i - 3, u, per):
                return -2  # B_k -> B_{k-1}
            return -1  # B_1 -> T_1
        t = self.btype(x, i, per)
        if t is not None and self.nonadj(u, t) and self.is_block(x, i - 2, u, per):
            # head on the relocated B_L of the u-belt ending at i-2
            if self.is_block(x, i - 4, u, per):
                return -3  # -> B_{L-1}
            return -2  # L = 1: -> T_1
        return 0

    def headmap(self, u, x, per):
        """p^{f_u}_x reduced mod per, as a list."""
        return [(i + self.cocycle(u, x, i, per)) % per for i in range(per)]


def is_perm(p):
    return len(set(p)) == len(p)


def compose(p, q):  # p o q
    return [p[q[i]] for i in range(len(q))]


def check_periodic(bl, per, x, stats):
    maps = [bl.headmap(u, x, per) for u in range(bl.n)]
    for u in range(bl.n):
        if not is_perm(maps[u]):
            print("NOT BIJECTIVE", bl.n, per, x, "u=", u, maps[u])
            return False
    for u in range(bl.n):
        for w in range(u + 1, bl.n):
            if bl.adj[u][w] and compose(maps[u], maps[w]) != compose(maps[w], maps[u]):
                print("NOT COMMUTING", bl.n, per, x, u, w)
                return False
            if not bl.adj[u][w] and compose(maps[u], maps[w]) != compose(maps[w], maps[u]):
                stats["noncommuting_witness"] += 1
    stats["configs"] += 1
    return True


# ---------------- RAAG words -----------------

def reduce_word(bl, syl):
    """Green normal form reduction of a syllable list [(type, exp)]."""
    syl = [s for s in syl if s[1] != 0]
    changed = True
    while changed:
        changed = False
        for i in range(len(syl)):
            u = syl[i][0]
            for k in range(i + 1, len(syl)):
                w = syl[k][0]
                if w == u:
                    e = syl[i][1] + syl[k][1]
                    rest = syl[:i] + syl[i + 1:k] + syl[k + 1:]
                    if e != 0:
                        rest.insert(i, (u, e))
                    syl = rest
                    changed = True
                    break
                if not bl.adj[u][w]:
                    break
            if changed:
                break
    return syl


def is_reduced(bl, syl):
    for i in range(len(syl)):
        u = syl[i][0]
        for k in range(i + 1, len(syl)):
            w = syl[k][0]
            if w == u:
                return False
            if not bl.adj[u][w]:
                break
    return True


def greedy_chain(bl, syl):
    idx = [len(syl) - 1]
    while True:
        cur = syl[idx[-1]][0]
        nxt = None
        for m in range(idx[-1] - 1, -1, -1):
            if not bl.adj[cur][syl[m][0]]:  # non-adjacent or equal
                nxt = m
                break
        if nxt is None:
            break
        assert syl[nxt][0] != cur, "reduced word has equal type in chain step"
        idx.append(nxt)
    return idx[::-1]


def chain_config(bl, syl):
    """Return (finite word padded with #, start head index) for the greedy chain."""
    chain = greedy_chain(bl, syl)
    pad = 8
    word = [bl.hash] * pad
    belt_ranges = []
    for m in chain:
        u, e = syl[m]
        start = len(word)
        for _ in range(abs(e)):
            word += [2 * u, 2 * u + 1]
        belt_ranges.append((start, abs(e)))
    word += [bl.hash] * pad
    last_start, last_len = belt_ranges[-1]
    head = last_start + 2 * last_len - 1  # unrelocated B_L of the last belt
    return word, head, chain


def apply_word_to_head(bl, syl, x, head):
    """Apply f_{s_1} o ... o f_{s_l} to the head (rightmost syllable first).
    x is a finite word padded with #; treat it as #^inf x #^inf by using a large period."""
    per = len(x)  # padding of 8 '#' on each side isolates the periodic copies
    h = head
    for (u, e) in reversed(syl):
        step = 1 if e > 0 else -1
        for _ in range(abs(e)):
            if step == 1:
                h = (h + bl.cocycle(u, x, h, per)) % per
            else:
                # inverse of the head permutation: find j with p(j) = h (|c| <= 3)
                cands = [j % per for j in range(h - 3, h + 4)
                         if (j + bl.cocycle(u, x, j, per)) % per == h]
                assert len(cands) == 1, cands
                h = cands[0]
    return h


def main():
    random.seed(20260916)
    graphs = {
        "K2": (2, [(0, 1)]),
        "2K1": (2, []),
        "P3": (3, [(0, 1), (1, 2)]),
        "K3+K1 (Z^3*Z)": (4, [(0, 1), (1, 2), (0, 2)]),
        "P4": (4, [(0, 1), (1, 2), (2, 3)]),
        "C4": (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
    }
    ok = True
    # 1+2: exhaustive periodic configurations
    for name, (n, edges) in graphs.items():
        bl = Belts(n, edges)
        stats = {"configs": 0, "noncommuting_witness": 0}
        maxper = {2: 7, 3: 6, 4: 5}[n]
        for per in range(1, maxper + 1):
            for x in itertools.product(bl.alphabet, repeat=per):
                if not check_periodic(bl, per, list(x), stats):
                    ok = False
                    break
        # random long periodic configurations, biased towards blocks
        for _ in range(3000):
            per = random.randint(8, 60)
            x = []
            while len(x) < per:
                r = random.random()
                if r < 0.8:
                    u = random.randrange(n)
                    x += [2 * u, 2 * u + 1]
                else:
                    x.append(random.choice(bl.alphabet))
            x = x[:per]
            if not check_periodic(bl, per, x, stats):
                ok = False
                break
        print(f"[bijective+commuting] {name}: {stats['configs']} periodic configs ok; "
              f"{stats['noncommuting_witness']} (config, nonadjacent pair) with noncommuting head maps")
    # 3: faithfulness on reduced words
    for name, (n, edges) in graphs.items():
        bl = Belts(n, edges)
        tested = 0
        exps = [-3, -2, -1, 1, 2, 3]
        for ell in range(1, 5):
            for types in itertools.product(range(n), repeat=ell):
                if any(types[i] == types[i + 1] for i in range(ell - 1)):
                    continue
                for ex in itertools.product(exps, repeat=ell):
                    syl = list(zip(types, ex))
                    if not is_reduced(bl, syl):
                        continue
                    word, head, chain = chain_config(bl, syl)
                    h = apply_word_to_head(bl, syl, word, head)
                    first_belt_T1 = 8
                    if h != first_belt_T1 or h == head:
                        print("FAITHFULNESS FAIL", name, syl, chain, head, h)
                        ok = False
                    tested += 1
        # random unreduced words: reduce, then the head test must succeed iff nonempty
        rnd = 0
        for _ in range(4000):
            ell = random.randint(1, 10)
            syl = [(random.randrange(n), random.choice(exps)) for _ in range(ell)]
            red = reduce_word(bl, syl)
            if not red:
                # trivial element: its head map must be the identity on random configs
                x = [random.choice(bl.alphabet) for _ in range(40)] + [bl.hash] * 8
                for s in range(0, 40, 3):
                    if apply_word_to_head(bl, syl, x, s) != s:
                        print("TRIVIAL WORD MOVES HEAD", name, syl)
                        ok = False
                rnd += 1
                continue
            word, head, chain = chain_config(bl, red)
            if apply_word_to_head(bl, syl, word, head) == head:
                print("UNREDUCED WORD FIXES HEAD", name, syl, red)
                ok = False
            rnd += 1
        print(f"[faithful] {name}: {tested} reduced words (length<=4, |exp|<=3) displace the head; "
              f"{rnd} random words consistent with normal form")
    print("ALL OK" if ok else "FAILURES FOUND")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
