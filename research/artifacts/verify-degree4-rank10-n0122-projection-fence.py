#!/usr/bin/env python3
"""Exact 68-scheme certificate for the rank-ten N(0;122) projection fence."""

from collections import defaultdict


def invert_letter(letter):
    return letter.swapcase()


def reduce_word(word):
    stack = []
    for letter in word:
        if stack and invert_letter(stack[-1]) == letter:
            stack.pop()
        else:
            stack.append(letter)
    return "".join(stack)


def inverse(word):
    return "".join(invert_letter(letter) for letter in reversed(word))


def multiply(*words):
    return reduce_word("".join(words))


def minimal(families):
    result = []
    for equations in sorted(set(families), key=lambda item: (len(item), sorted(item))):
        if not any(old <= equations for old in result):
            result.append(equations)
    return result


def identity_schemes(syllables):
    states = {((), frozenset())}
    for copy, coefficient in syllables:
        following = set()
        for stack, equations in states:
            following.add((stack, equations | {coefficient}))
            if stack and stack[-1][0] == copy:
                combined = multiply(stack[-1][1], coefficient)
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
                  for equations in minimal(families)}
    return minimal([equations for stack, equations in states if not stack])


def substitute(word, variable, image):
    result = ""
    for letter in word:
        if letter.lower() == variable:
            result += image if letter.islower() else inverse(image)
        else:
            result += letter
    return reduce_word(result)


def eliminate(equations, target):
    equations = sorted(word for word in equations if word)
    substitutions = []
    while True:
        choice = None
        for index, equation in enumerate(equations):
            for variable in "aduv":
                positions = [j for j, letter in enumerate(equation)
                             if letter.lower() == variable]
                if len(positions) == 1:
                    choice = index, variable, positions[0]
                    break
            if choice:
                break
        if not choice:
            return equations, target, substitutions
        index, variable, position = choice
        equation = equations.pop(index)
        left, letter, right = (equation[:position], equation[position],
                               equation[position + 1:])
        image = (multiply(inverse(left), inverse(right)) if letter.islower()
                 else multiply(right, left))
        substitutions.append((variable, image))
        equations = [substitute(word, variable, image) for word in equations]
        equations = sorted(word for word in equations if word)
        target = substitute(target, variable, image)


# First impose K1=K2=K3=1:
# c=a d^-1 a, b=d c^-1 d, p=b^-1 d b^-1.
a, d, u, v = "a", "d", "u", "v"
c = multiply(a, inverse(d), a)
b = multiply(d, inverse(c), d)
p = multiply(inverse(b), d, inverse(b))
carrier = (
    (0, c), (1, d), (2, a), (3, multiply(b, p, a, inverse(b))),
    (2, inverse(a)), (1, inverse(d)),
    (0, multiply(inverse(c), inverse(v), inverse(u))),
    (1, a), (2, b), (3, multiply(c, inverse(b))),
    (2, inverse(a)), (1, inverse(d)),
    (0, multiply(inverse(c), d, u)),
)
target = multiply(inverse(c), b, inverse(c), a, inverse(c), v, c)
schemes = identity_schemes(carrier)
assert len(schemes) == 68

resolved = 0
residues = []
for index, equations in enumerate(schemes):
    remaining, reduced_target, substitutions = eliminate(equations, target)
    if not reduced_target:
        resolved += 1
    else:
        residues.append((index, remaining, reduced_target, substitutions))

assert resolved == 67
assert len(residues) == 1
index, remaining, reduced_target, substitutions = residues[0]
assert reduced_target == "aaaaaaa"
assert {reduce_word(word) for word in remaining} == {
    "AAAAA", "AAAA", "AAA", "aaa", "aa"
}
print("schemes 68 freely_resolved 67")
print("residue", index, "substitutions", substitutions)
print("residue relations", tuple(remaining), "target", reduced_target)
print("gcd(5,4)=1 forces a=1; target=1")
