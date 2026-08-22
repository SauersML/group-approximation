#!/usr/bin/env python3
"""Exact free-product branch splitter for the two balanced rank-nine classes."""

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
    for copy, coefficient in word:
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
        grouped = defaultdict(list)
        for stack, equations in following:
            grouped[stack].append(equations)
        states = {(stack, equations) for stack, families in grouped.items()
                  for equations in minimal_families(families)}
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
    "classA-eq2": concatenate(inverse_free(H), C0, H, A1),
    "classA-eq3": concatenate(inverse_free(H), C1, inverse_free(H), E2),
    "classB-eq1": concatenate(H, A0, H, E3),
    "classB-eq2": concatenate(inverse_free(H), C0, H, A1),
    "classB-eq3": concatenate(inverse_free(H), C1, inverse_free(H), E4,
                               inverse_free(H), E5),
}


def show_coefficient(word):
    if not word:
        return "1"
    return " ".join(("g" if letter > 0 else "g") + str(abs(letter) - 1) +
                    ("^-1" if letter < 0 else "") for letter in word)


for name, word in systems.items():
    schemes = identity_schemes(word)
    print(name, "syllables", len(word), "minimal_schemes", len(schemes))
    for index, equations in enumerate(schemes):
        print(" BRANCH", index, tuple(show_coefficient(equation)
                                      for equation in sorted(equations)))
