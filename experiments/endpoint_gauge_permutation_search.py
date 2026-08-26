#!/usr/bin/env python3
"""Bounded permutation search for the endpoint/native gauge presentation.

Run remotely (MSI), not as a local exhaustive computation.
"""

from __future__ import annotations

import itertools
import sys


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Return p*q, acting by q first and then p."""
    return tuple(p[q[i]] for i in range(len(p)))


def power(p: tuple[int, ...], exponent: int) -> tuple[int, ...]:
    out = tuple(range(len(p)))
    for _ in range(exponent):
        out = compose(out, p)
    return out


def involutions(n: int):
    ident = tuple(range(n))
    for p in itertools.permutations(range(n)):
        if compose(p, p) == ident:
            yield p


def standard_s3(n: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    e = list(range(n))
    f = list(range(n))
    e[0], e[1] = e[1], e[0]
    f[1], f[2] = f[2], f[1]
    return tuple(e), tuple(f)


def eval_word(word: str, values: dict[str, tuple[int, ...]]) -> tuple[int, ...]:
    out = tuple(range(len(next(iter(values.values())))))
    for letter in word:
        out = compose(out, values[letter])
    return out


RELATOR = "HEHEFHF EHEFHF".replace(" ", "")


def main() -> None:
    maximum = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for n in range(3, maximum + 1):
        ident = tuple(range(n))
        e, f = standard_s3(n)
        count = 0
        models = []
        for h in involutions(n):
            count += 1
            values = {"H": h, "E": e, "F": f}
            if power(compose(h, e), 4) != ident:
                continue
            if power(compose(h, f), 4) != ident:
                continue
            if eval_word(RELATOR, values) != ident:
                continue
            models.append(h)
            if len(models) == 3:
                break
        print(n, count, len(models), models)


if __name__ == "__main__":
    main()
