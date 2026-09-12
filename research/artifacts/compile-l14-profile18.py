#!/usr/bin/env python3
"""Compile the two rank-nine classes for profile ---++-++++-+++.

The compiler starts from the literal four copy-corners.  It does not use a
matrix transpose as an inverse: inversion reverses both free-product
syllables and coefficient letters.
"""

import argparse


def reduce_coefficient(word):
    out = []
    for letter in word:
        if out and out[-1] == (letter[0], -letter[1]):
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def syllable(copy, *names):
    return copy, tuple((name, 1) for name in names)


def multiply(*words):
    out = []
    for word in words:
        for copy, coefficient in word:
            if not coefficient:
                continue
            if out and out[-1][0] == copy:
                coefficient = reduce_coefficient(out[-1][1] + coefficient)
                out.pop()
                if coefficient:
                    out.append((copy, coefficient))
            else:
                out.append((copy, coefficient))
    return tuple(out)


def inverse(word):
    return tuple((copy, tuple((name, -sign)
                              for name, sign in reversed(coefficient)))
                 for copy, coefficient in reversed(word))


def power(word, sign):
    return word if sign > 0 else inverse(word)


def corner(entries):
    return tuple(syllable(copy, f"g{slot}") for copy, slot in entries)


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def raw_corners(signs, start):
    """Replay the ranker's literal z-height decomposition."""
    height, raw = start, []
    for slot, sign in enumerate(signs):
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(raw, quotient)
        raw.append(("g", residue, slot))
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
        stable_sign = expanded[index][1]
        index += 1
        entries = []
        while index < len(expanded) and expanded[index][0] != "z":
            _, copy, slot = expanded[index]
            entries.append((copy, slot))
            index += 1
        result.append((stable_sign, corner(tuple(entries))))
    return tuple(result)


H = corner(((0, 9), (1, 10), (0, 11), (1, 12), (2, 13),
            (3, 0), (2, 1), (1, 2), (0, 3), (1, 4), (2, 5),
            (1, 6), (2, 7), (3, 8)))

FACES = (
    ((-1, corner(((3, 1), (2, 2), (1, 3), (2, 4), (3, 5),
                  (2, 6), (3, 7)))),
     (1, corner(((0, 8), (1, 9), (2, 10), (1, 11), (2, 12),
                 (3, 13)))),
     (1, corner(((0, 0),)))),
    ((-1, corner(((3, 2), (2, 3), (3, 4)))),
     (1, corner(((0, 5),))),
     (-1, corner(((3, 6),))),
     (1, corner(((0, 7), (1, 8), (2, 9), (3, 10), (2, 11),
                 (3, 12)))),
     (1, corner(((0, 13), (1, 0), (0, 1))))),
    ((-1, corner(((3, 3),))),
     (1, corner(((0, 4), (1, 5), (0, 6), (1, 7), (2, 8),
                 (3, 9)))),
     (1, corner(((0, 10),))),
     (-1, corner(((3, 11),))),
     (1, corner(((0, 12), (1, 13), (2, 0), (1, 1), (0, 2))))),
)

PROFILE = tuple(1 if sign == "+" else -1 for sign in "---++-++++-+++")
RAW = tuple(raw_corners(PROFILE, start) for start in range(4))
assert RAW[3] == ((1, H),)
assert FACES == RAW[:3]

# One literal representative per cyclic class, copied from rank job 16684537.
# Each item is (cyclic face indices, (target generator, target exponent)).
SELECTIONS = {
    "N0131": (
        (((0,), (1, 1)), ((1,), (2, 1)), ((2,), (0, 1))),
        (((4, 0), (2, -1)), ((1, 2), (3, 1)), ((3,), (4, 1))),
        (((0,), (0, -1)), ((1, 2, 3), (4, -1)), ((4,), (5, 1))),
    ),
    "I0131": (
        (((0,), (2, -1)), ((1,), (1, -1)), ((2,), (0, -1))),
        (((0, 1, 2), (4, -1)), ((3,), (3, -1)), ((4,), (2, 1))),
        (((0,), (0, 1)), ((1, 2, 3), (5, -1)), ((4,), (4, 1))),
    ),
}


def atom(face_index, atom_index):
    stable_sign, coefficient = FACES[face_index][atom_index]
    return multiply(power(H, -stable_sign), coefficient)


def cyclic_contiguous(indices, valence):
    return all(right == (left + 1) % valence
               for left, right in zip(indices, indices[1:]))


def compile_selection(selection):
    occurrences = {name: [] for name in range(6)}
    for face_index, grouping in enumerate(selection):
        flattened = sum((indices for indices, _ in grouping), ())
        assert sorted(flattened) == list(range(len(FACES[face_index])))
        assert all(cyclic_contiguous(indices, len(FACES[face_index]))
                   for indices, _ in grouping)
        for indices, (name, sign) in grouping:
            word = multiply(*(atom(face_index, index) for index in indices))
            occurrences[name].append((sign, word))
    relations = {}
    for name in (0, 2, 4):
        assert sorted(sign for sign, _ in occurrences[name]) == [-1, 1]
        positive = next(word for sign, word in occurrences[name] if sign > 0)
        negative = next(word for sign, word in occurrences[name] if sign < 0)
        relations[f"R{name}"] = multiply(positive, negative)
    for name in (1, 3, 5):
        assert len(occurrences[name]) == 1
    relations["K"] = multiply(*(power(occurrences[name][0][1],
                                            occurrences[name][0][0])
                                for name in (1, 3, 5)))
    return relations


def project(word, target):
    out = ()
    for copy, coefficient in word:
        if copy == target:
            out = reduce_coefficient(out + coefficient)
    return out


def show(name, word):
    print(f"{name}_syllables={len(word)}")
    print(f"{name}_colors=" + ",".join(str(copy) for copy, _ in word))
    for index, (copy, coefficient) in enumerate(word):
        text = " ".join(letter + ("^-1" if sign < 0 else "")
                        for letter, sign in coefficient)
        print(f"{name}[{index}]={copy}:{text}")
    for target in range(4):
        coefficient = project(word, target)
        text = " ".join(letter + ("^-1" if sign < 0 else "")
                        for letter, sign in coefficient)
        print(f"{name}_projection_{target}={text or '1'}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("class_name", choices=tuple(SELECTIONS))
    args = parser.parse_args()
    print(f"class={args.class_name}")
    print(f"H_syllables={len(H)}")
    for name, word in compile_selection(SELECTIONS[args.class_name]).items():
        show(name, word)


if __name__ == "__main__":
    main()
