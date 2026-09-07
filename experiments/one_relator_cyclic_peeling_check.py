#!/usr/bin/env python3
"""Check exact word identities and finite cyclic-peeling schedules.

This deterministic stdlib-only replay checks the algebra in
research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md.
It does not certify Bass-Serre theory, sofic permanence, or an infinite
group's soficity. Those arguments are supplied by the written proof.
"""

import argparse
from collections import Counter
from itertools import product
import json
import random


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def reduced(word):
    stack = []
    for name, sign in word:
        require(sign in (-1, 1), "invalid letter sign")
        if stack and stack[-1] == (name, -sign):
            stack.pop()
        else:
            stack.append((name, sign))
    return tuple(stack)


def mul(*words):
    return reduced(letter for word in words for letter in word)


def inv(word):
    return tuple((name, -sign) for name, sign in reversed(word))


def power(word, exponent):
    block = word if exponent >= 0 else inv(word)
    return mul(*(block for _ in range(abs(exponent))))


def gen(name):
    return ((name, 1),)


def conj(word, by):
    return mul(inv(by), word, by)


def substitute(word, images):
    return mul(*(power(images.get(name, gen(name)), sign) for name, sign in word))


A, B = gen("a"), gen("b")


def indexed(index):
    return gen(f"a[{index}]")


def index_of(name):
    require(name.startswith("a[") and name.endswith("]"), "invalid index name")
    return int(name[2:-1])


def decode(word):
    return mul(*(conj(power(A, sign), power(B, index_of(name)))
                 for name, sign in word))


def rewrite(word):
    """Independent height scan, using a_j=b^(-j)ab^j."""
    height, output = 0, []
    for name, sign in word:
        if name == "b":
            height += sign
        elif name == "a":
            output.append((f"a[{-height}]", sign))
        else:
            raise ValueError("expected a word in a,b")
    if height:
        raise ValueError("nonzero b-exponent sum")
    return reduced(output)


def relator(w, left, right):
    return mul(conj(power(A, left), conj(A, w)), power(A, -right))


def indexed_relation(x, y, z, block, left, right):
    c = conj(y, power(z, block))
    return mul(conj(power(x, left), c), power(x, -right))


def case_of(p, q, block):
    d = p + q
    if block == 0:
        return "zero-block"
    if p == 0:
        return "zero-prefix"
    if q == 0:
        return "zero-suffix"
    if d == 0:
        return "diagonal"
    return {0: "new-x", d: "new-y", q: "new-z"}[min(0, d, q)]


def check_schedule(d, q, indices):
    require(len({0, d, q}) == 3, "three distinct indices required")
    minimum = min(0, d, q)
    targets = {i + minimum for i in indices}
    universe = {i + offset for i in indices for offset in (0, d, q)}
    old = universe - targets
    for i in sorted(indices, reverse=True):
        new = i + minimum
        dependencies = {i, i + d, i + q} - {new}
        require(new not in old, "target is not new")
        require(dependencies <= old, "unavailable dependency")
        old.add(new)
    require(old == universe, "incomplete schedule")


def check_one_sided(d, v):
    if d <= 0 or any(index_of(name) <= 0 for name, _ in v):
        raise ValueError("strictly positive support required")


def replay():
    counts, cases = Counter(), Counter()
    nonzero = (-2, -1, 1, 2)
    for p, q, block, left, right in product(
            range(-3, 4), range(-3, 4), range(-2, 3), nonzero, nonzero):
        d = p + q
        w = mul(power(B, p), power(A, block), power(B, q))
        require(w == mul(power(B, d), decode(power(indexed(q), block))),
                ("factorization", p, q, block))
        original = relator(w, left, right)
        case = case_of(p, q, block)
        cases[case] += 1
        for shift in (-2, 0, 3):
            literal = conj(original, power(B, shift))
            scanned = rewrite(literal)
            expected = indexed_relation(indexed(shift), indexed(shift + d),
                                        indexed(shift + q), block, left, right)
            require(scanned == expected, ("kernel formula", p, q, block, shift))
            require(decode(scanned) == literal, "rewrite round trip")
            counts["schreier_identities"] += 1
        if case == "zero-block":
            require(original == relator(power(B, d), left, right), "zero block")
        elif case == "zero-prefix":
            require(original == relator(power(B, q), left, right), "zero prefix")
        elif case == "zero-suffix":
            require(mul(power(A, block), original, power(A, -block))
                    == relator(power(B, p), left, right), "zero suffix")
        if d == 0 and (block == 0 or p == 0 or q == 0):
            require(original == power(A, left - right), "cyclic degeneration")
        counts["single_block_parameters"] += 1

    x, y, z, t, h = map(gen, ("x", "y", "z", "t", "h"))
    for block, left, right in product(nonzero, repeat=3):
        target = indexed_relation(x, y, z, block, left, right)
        bs = mul(conj(power(x, left), t), power(x, -right))
        require(substitute(bs, {"t": conj(y, power(z, block))}) == target,
                "new-x elimination")
        v = mul(power(z, block), x, power(z, -block))
        hnn = mul(conj(power(v, left), y), power(v, -right))
        require(hnn == mul(power(z, block), target, power(z, -block)),
                "new-y conjugation")
        eliminated = substitute(substitute(bs, {"t": conj(y, h)}),
                                 {"h": power(z, block)})
        require(eliminated == target, "new-z elimination")
        require(substitute(eliminated, {"y": x})
                == indexed_relation(x, x, z, block, left, right), "diagonal block")
        counts["attachment_identity_sets"] += 1

    for d, q in product(range(-5, 6), repeat=2):
        if len({0, d, q}) == 3:
            for indices in ((), (-3,), (-4, 2, 5), tuple(range(-4, 5))):
                check_schedule(d, q, indices)
                counts["finite_peeling_schedules"] += 1

    rng = random.Random(20260907)
    for _ in range(600):
        d = rng.randrange(1, 6)
        v = reduced((f"a[{rng.randrange(1, 7)}]", rng.choice((-1, 1)))
                    for _ in range(rng.randrange(13)))
        check_one_sided(d, v)
        left, right = rng.choice(nonzero), rng.choice(nonzero)
        original = relator(mul(power(B, d), decode(v)), left, right)
        for shift in (-3, 0, 2):
            vi = tuple((f"a[{index_of(name) + shift}]", sign) for name, sign in v)
            c = conj(indexed(shift + d), vi)
            expected = mul(conj(power(indexed(shift), left), c),
                           power(indexed(shift), -right))
            require(rewrite(conj(original, power(B, shift))) == expected,
                    "one-sided formula")
            counts["one_sided_identities"] += 1

    for d, v in ((0, ()), (-1, ()), (1, indexed(0)), (1, indexed(-2))):
        try:
            check_one_sided(d, v)
        except ValueError:
            counts["negative_controls"] += 1
        else:
            raise AssertionError("unsupported support accepted")
    try:
        rewrite(B)
    except ValueError:
        counts["negative_controls"] += 1
    else:
        raise AssertionError("nonkernel word accepted")
    sample = mul(power(B, -1), A, power(B, 2))
    require(conj(A, sample) == decode(conj(indexed(1), indexed(2))),
            "Berlai example convention")
    require(set(cases) == {"new-x", "new-y", "new-z", "diagonal", "zero-block",
                          "zero-prefix", "zero-suffix"}, "unexercised case")
    return {
        "all_passed": True,
        "scope": "Exact free-group identities and finite dependency schedules only.",
        "not_checked": ["Sofic permanence", "Bass-Serre normal forms",
                        "Lean formalization", "Universal one-relator soficity"],
        "counts": dict(sorted(counts.items())),
        "single_block_case_counts": dict(sorted(cases.items())),
        "random_seed": 20260907,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = replay()
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("PASS: exact identities and finite peeling schedules")
        print(json.dumps(result["counts"], sort_keys=True))
        print(result["scope"])
