#!/usr/bin/env python3
"""Rook-independent forward tables of shape ns x nm and their presentations P(T).

Labels: S = {1, s1, ..., s_(ns-1)}, M = {1, m1, ..., m_(nm-1)}.
Forward cell (s, m) is the word x_s x_m (x_1 = 1).  A table is a set partition of
the cells in which no block contains two cells of one row or one column.
P(T) = < x_a (a != 1) | x_s x_m = x_s' x_m' for cells in one block >.

Words are tuples of nonzero ints: generator i is i+1, its inverse -(i+1).
Generator order: s1..s_(ns-1), m1..m_(nm-1).
"""
import itertools


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]
        yield [[first]] + part


def independent(block):
    rows = [c[0] for c in block]
    cols = [c[1] for c in block]
    return len(set(rows)) == len(rows) and len(set(cols)) == len(cols)


def gen_names(ns, nm):
    return [f"s{i}" for i in range(1, ns)] + [f"m{i}" for i in range(1, nm)]


def label_word(ns, nm, kind, idx):
    """Word of label s_idx (kind 's') or m_idx (kind 'm'); idx 0 is the label 1."""
    if idx == 0:
        return ()
    if kind == "s":
        return (idx,)
    return (ns - 1 + idx,)


def inv(w):
    return tuple(-x for x in reversed(w))


def tables(ns, nm):
    """Yield (partition, relators) for every rook-independent partition."""
    cells = [(s, m) for s in range(ns) for m in range(nm)]
    for part in set_partitions(cells):
        if not all(independent(b) for b in part):
            continue
        rels = []
        for b in part:
            s0, m0 = b[0]
            w0 = label_word(ns, nm, "s", s0) + label_word(ns, nm, "m", m0)
            for (s, m) in b[1:]:
                w = label_word(ns, nm, "s", s) + label_word(ns, nm, "m", m)
                rels.append(w0 + inv(w))
        yield part, rels


def rook_partitions(ns, nm):
    """Direct generator of the rook-independent partitions of the ns x nm grid:
    each cell, in row-major order, joins a block with no cell in its row or column,
    or opens a new block.  Yields the same set as the filtered set_partitions."""
    cells = [(s, m) for s in range(ns) for m in range(nm)]
    blocks = []

    def rec(k):
        if k == len(cells):
            yield [list(b) for b in blocks]
            return
        s, m = cells[k]
        for b in blocks:
            if all(c[0] != s and c[1] != m for c in b):
                b.append((s, m))
                yield from rec(k + 1)
                b.pop()
        blocks.append([(s, m)])
        yield from rec(k + 1)
        blocks.pop()

    yield from rec(0)


def relators(ns, nm, part):
    rels = []
    for b in part:
        s0, m0 = b[0]
        w0 = label_word(ns, nm, "s", s0) + label_word(ns, nm, "m", m0)
        for (s, m) in b[1:]:
            w = label_word(ns, nm, "s", s) + label_word(ns, nm, "m", m)
            rels.append(w0 + inv(w))
    return rels


def tables_fast(ns, nm):
    for part in rook_partitions(ns, nm):
        yield part, relators(ns, nm, part)


if __name__ == "__main__":
    for shape in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        n = sum(1 for _ in tables(*shape))
        n2 = sum(1 for _ in tables_fast(*shape))
        a = sorted(sorted(sorted(b) for b in p) for p, _ in tables(*shape))
        c = sorted(sorted(sorted(b) for b in p) for p, _ in tables_fast(*shape))
        print(shape, n, n2, "same" if a == c else "DIFFERENT")
    for shape in [(2, 4), (3, 4)]:
        print(shape, sum(1 for _ in rook_partitions(*shape)))
