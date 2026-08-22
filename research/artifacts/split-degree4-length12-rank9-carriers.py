#!/usr/bin/env python3
"""Exact free-product branch splitter for the two balanced rank-nine classes."""

import argparse
from collections import defaultdict


def reduce_coefficient(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inverse_coefficient(word):
    return tuple(-letter for letter in reversed(word))


def inverse_free(word):
    return tuple((copy, inverse_coefficient(coefficient))
                 for copy, coefficient in reversed(word))


def concatenate(*words):
    return tuple(item for word in words for item in word)


def minimal_families(families):
    result = []
    for equations in sorted(set(families), key=lambda x: (len(x), x)):
        if any(old <= equations for old in result):
            continue
        result.append(equations)
    return result


def identity_schemes(word):
    states = {((), frozenset())}
    for position, (copy, coefficient) in enumerate(word):
        following = set()
        for stack, equations in states:
            following.add((stack, equations | {coefficient}))
            if stack and stack[-1][0] == copy:
                combined = reduce_coefficient(stack[-1][1] + coefficient)
                if combined:
                    following.add((stack[:-1] + ((copy, combined),), equations))
                    following.add((stack[:-1], equations | {combined}))
                else:
                    following.add((stack[:-1], equations))
            else:
                following.add((stack + ((copy, coefficient),), equations))
        remaining = len(word) - position - 1
        grouped = defaultdict(list)
        for stack, equations in following:
            if len(stack) > remaining:
                continue
            grouped[stack].append(equations)
        states = {(stack, equations) for stack, families in grouped.items()
                  for equations in minimal_families(families)}
        print(" progress", position + 1, len(states), flush=True)
    return minimal_families([equations for stack, equations in states if not stack])


def g(index):
    return (index + 1,)


H = tuple((copy, g(index)) for index, copy in enumerate(
    (0, 1, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3)))
A0 = tuple((copy, g(index)) for index, copy in
           zip(range(1, 8), (3, 2, 1, 2, 1, 2, 3)))
B0 = tuple((copy, g(index)) for index, copy in
           zip(range(8, 12), (0, 1, 2, 3)))
C0 = ((0, g(0)),)
A1 = tuple((copy, g(index)) for index, copy in
           zip(range(2, 7), (3, 2, 3, 2, 3)))
B1 = tuple((copy, g(index)) for index, copy in
           zip(range(7, 11), (0, 1, 2, 3)))
C1 = ((0, g(11)), (1, g(0)), (0, g(1)))
E1, E2, E3 = ((3, g(3)),), ((0, g(4)),), ((3, g(5)),)
E4 = tuple((copy, g(index)) for index, copy in
           zip(range(6, 10), (0, 1, 2, 3)))
E5 = tuple((copy, g(index)) for index, copy in
           zip((10, 11, 0, 1, 2), (0, 1, 2, 1, 0)))

systems = {
    "classA-eq1": concatenate(H, A0, H, E1),
    "classA-eq3": concatenate(inverse_free(H), C1, inverse_free(H), E2),
    "classB-eq1": concatenate(H, A0, H, E3),
    "classB-eq3": concatenate(inverse_free(H), C1, inverse_free(H), E4,
                               inverse_free(H), E5),
}


def substitute_coefficient(word, replacement):
    result = ()
    for letter in word:
        image = replacement.get(abs(letter) - 1, (abs(letter),))
        if letter < 0:
            image = inverse_coefficient(image)
        result = reduce_coefficient(result + image)
    return result


def substitute_free(word, replacement):
    return tuple((copy, substitute_coefficient(coefficient, replacement))
                 for copy, coefficient in word)


# The common Q carrier equation is first solved by malnormality.  It forces
# g0=1 and A1=1.  The alternating five-syllable A1 has exactly two branches.
branches = {
    "I": {0: (), 3: (), 5: (), 6: (-5, -3)},
    "II": {0: (), 4: (), 5: (-4,), 6: (-3,)},
}


def show_coefficient(word):
    if not word:
        return "1"
    return " ".join(("g" if letter > 0 else "g") + str(abs(letter) - 1) +
                    ("^-1" if letter < 0 else "") for letter in word)


parser = argparse.ArgumentParser()
tasks = tuple((name, word, branch_name, replacement)
              for name, word in systems.items()
              for branch_name, replacement in branches.items())
parser.add_argument("--task", type=int, choices=range(len(tasks)), required=True)
args = parser.parse_args()
name, word, branch_name, replacement = tasks[args.task]
name += "-branch" + branch_name
word = substitute_free(word, replacement)
for name, word in ((name, word),):
    schemes = identity_schemes(word)
    print(name, "syllables", len(word), "minimal_schemes", len(schemes))
    for index, equations in enumerate(schemes):
        print(" BRANCH", index, tuple(show_coefficient(equation)
                                      for equation in sorted(equations)))
