#!/usr/bin/env python3
"""Evolutionary exact search in the branch-A projection kernel.

The search is heuristic, but every fitness evaluation and reported hit uses
the faithful Bergman chart and actual multiplicative inverses.
"""

import argparse
import importlib.util
import random
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def elt(value, inverse):
    assert P.mul(value, inverse) == P.ONE == P.mul(inverse, value)
    return value, inverse


def mul(*elements):
    value = inverse = P.ONE
    for forward, backward in elements:
        value = P.mul(value, forward)
        inverse = P.mul(backward, inverse)
    return value, inverse


def inv(element):
    return element[1], element[0]


ONE = elt(P.ONE, P.ONE)
base = {
    "a": elt(P.A, P.A), "b": elt(P.B, P.B),
    "c": elt(P.C, P.C), "d": elt(P.D, P.D),
    "e": elt(P.E, P.E), "r": elt(P.R, P.RINV),
    "p": elt(P.P, P.PINV),
}
alphabet = tuple(base) + tuple(name.upper() for name in base)


def value(word):
    return mul(*(inv(base[x.lower()]) if x.isupper() else base[x]
                 for x in word)) if word else ONE


def inverse_word(word):
    return tuple(x.lower() if x.isupper() else x.upper()
                 for x in reversed(word))


def reducew(word):
    stack = []
    for copy, element in word:
        if element[0] == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            element = mul(stack.pop()[1], element)
            if element[0] == P.ONE:
                continue
        stack.append((copy, element))
    return tuple(stack)


def invw(word):
    return tuple((copy, inv(element)) for copy, element in reversed(word))


def replay(genome):
    rw, sw, aw, kw, tbit = genome
    r, s, a, k = map(value, (rw, sw, aw, kw))
    vv = mul(k, base["c"], inv(k))
    t = vv if tbit else ONE
    q = mul(inv(r), inv(t))
    b, c = mul(q, vv), mul(a, vv)
    H = reducew(((0, b), (1, c), (2, q), (3, a)))
    B0 = reducew(((0, a), (1, b), (2, c), (3, inv(r))))
    B1 = reducew(((0, q), (1, a), (2, b), (3, c)))
    E1 = ((3, t),)
    E5 = ((0, mul(c, s)),)
    E4 = reducew(((0, inv(s)), (1, q), (2, a), (3, b)))
    K = reducew(invw(H) + B0 + invw(H) + B1 + invw(E1) +
                invw(H) + invw(E5) + H + invw(E4) + H)
    return K


def random_word(rng, maximum=8):
    return tuple(rng.choice(alphabet) for _ in range(rng.randrange(maximum + 1)))


def random_genome(rng):
    return (random_word(rng), random_word(rng), random_word(rng),
            random_word(rng), rng.randrange(2))


def mutate(rng, genome):
    words = [list(word) for word in genome[:4]]
    bit = genome[4]
    index = rng.randrange(5)
    if index == 4:
        bit ^= 1
    else:
        word = words[index]
        operation = rng.randrange(3)
        if operation == 0 and len(word) < 10:
            word.insert(rng.randrange(len(word) + 1), rng.choice(alphabet))
        elif operation == 1 and word:
            word.pop(rng.randrange(len(word)))
        elif word:
            word[rng.randrange(len(word))] = rng.choice(alphabet)
        else:
            word.append(rng.choice(alphabet))
    return tuple(tuple(word) for word in words) + (bit,)


parser = argparse.ArgumentParser()
parser.add_argument("--seed", type=int, required=True)
parser.add_argument("--steps", type=int, default=250000)
args = parser.parse_args()
rng = random.Random(args.seed)
population = [random_genome(rng) for _ in range(64)]
best = 10**9
for step in range(args.steps):
    parent = population[rng.randrange(len(population))]
    genome = mutate(rng, parent) if rng.random() < .85 else random_genome(rng)
    K = replay(genome)
    score = len(K)
    if score == 1 and K[0][1][0] != P.ONE:
        print("HIT", "seed", args.seed, "step", step, "genome", genome,
              "copy", K[0][0], "mark", K[0][1][0], flush=True)
        raise SystemExit(42)
    if score < best:
        best = score
        print("BEST", best, "step", step, "genome", genome, flush=True)
    victim = rng.randrange(len(population))
    old_score = len(replay(population[victim]))
    if score <= old_score or rng.random() < .01:
        population[victim] = genome
    if step % 1000 == 0:
        P.mul.cache_clear()
print("seed", args.seed, "steps", args.steps, "best", best, "hits 0")
