#!/usr/bin/env python3
"""Derive all one-copy retractions in the d4 (1,3,3,3) topology."""


def inverse_unit(word):
    return tuple(-letter - 1 for letter in reversed(word))


def multiply_unit(left, right):
    stack = list(left)
    for letter in right:
        if stack and stack[-1] == -letter - 1:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def reduce_word(word):
    stack = []
    for copy, unit in word:
        if stack and stack[-1][0] == copy:
            unit = multiply_unit(stack.pop()[1], unit)
        if unit:
            stack.append((copy, unit))
    return tuple(stack)


def inverse_word(word):
    return tuple((copy, inverse_unit(unit)) for copy, unit in reversed(word))


def multiply_words(*words):
    return reduce_word(sum(words, ()))


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def corners(start):
    signs = (-1, -1, -1, 1, 1, 1, 1, 1, 1, 1)
    height, raw = start, []
    for slot, sign in enumerate(signs):
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(raw, quotient)
        raw.append(("g", residue, (slot,)))
        append_z(raw, -quotient)
        height += sign
    append_z(raw, 1)
    expanded = []
    for token in raw:
        if token[0] == "z":
            expanded.extend(("z", 1 if token[1] > 0 else -1)
                            for _ in range(abs(token[1])))
        else:
            expanded.append(token)
    cut = next(index for index, token in enumerate(expanded)
               if token[0] == "z")
    expanded = expanded[cut:] + expanded[:cut]
    result, index = [], 0
    while index < len(expanded):
        sign = expanded[index][1]
        index += 1
        corner = []
        while index < len(expanded) and expanded[index][0] != "z":
            _, copy, unit = expanded[index]
            corner.append((copy, unit))
            index += 1
        result.append((sign, reduce_word(tuple(corner))))
    return tuple(result)


def evaluate(data, pivot):
    result = ()
    for sign, corner in data:
        result = multiply_words(result,
                                pivot if sign < 0 else inverse_word(pivot),
                                corner)
    return result


def retract(word, copy):
    unit = ()
    for factor_copy, factor in word:
        if factor_copy == copy:
            unit = multiply_unit(unit, factor)
    return unit


def show(unit):
    return " ".join(("g" if letter >= 0 else "g")
                    + str(letter if letter >= 0 else -letter - 1)
                    + ("" if letter >= 0 else "^-1") for letter in unit) or "1"


data = tuple(corners(start) for start in range(4))
pivot = data[3][0][1]
for residual in range(3):
    word = evaluate(data[residual], pivot)
    for copy in range(4):
        print(f"R{residual}|{copy} = {show(retract(word, copy))}")
