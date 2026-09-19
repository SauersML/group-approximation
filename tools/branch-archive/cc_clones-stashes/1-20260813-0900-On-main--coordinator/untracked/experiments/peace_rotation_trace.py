#!/usr/bin/env python3
"""Check the finite PEACE proof trace for the CRW rotation presentation.

This is a proof-object extraction aid, not a group-word solver.  It checks
only free reduction and that every parenthesized proof item is a cyclic
conjugate of one of the eight displayed defining relators (or its inverse).
The resulting item list is intended for replay inside Lean.
"""

TRACE = """
xYX(x^3)(XZ)^3(ZxYX)^2xyX[z][xy]X(z^2)x[z]x(z^2)X^2(x^3)(XZ)^3x[YX][Z][xy](Y^3)y
(yXzx)^2(zy)^3Y[Z]Y(Z^2)y[YX][Z]X(Z^2)x[YX][Z][xy](Y^3)yX(xyXz)^2(zx)^3(X^3)xYx
YX(x^3)(XZ)^3(ZxYX)^2xyX[z][xy]X(z^2)x[z]x(z^2)X^2(x^3)(XZ)^3x[YX][Z][xy](Y^3)y
(yXzx)^2(zy)^3Y[Z]Y(Z^2)y[YX][Z]X(Z^2)x[YX][Z][xy]Y^2X(xyXz)^2(zx)^3(X^3)xy^2
""".replace("\n", "")


def inverse(word):
    return "".join(c.swapcase() for c in reversed(word))


def reduce_word(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == letter.swapcase():
            stack.pop()
        else:
            stack.append(letter)
    return "".join(stack)


def expanded_atom(text):
    """Expand letter powers in a word having no proof-item delimiters."""
    out = []
    i = 0
    while i < len(text):
        letter = text[i]
        assert letter.lower() in "xyz", (i, text[i:])
        i += 1
        power = 1
        if i < len(text) and text[i] == "^":
            i += 1
            j = i
            while j < len(text) and text[j].isdigit():
                j += 1
            assert j > i
            power = int(text[i:j])
            i = j
        out.append(letter * power)
    return "".join(out)


def tokens(trace):
    """Return `(kind, expanded_word)` with kinds raw/relator/subgroup."""
    answer = []
    i = 0
    while i < len(trace):
        opening = trace[i]
        if opening in "([":
            closing = ")" if opening == "(" else "]"
            j = trace.index(closing, i + 1)
            word = expanded_atom(trace[i + 1:j])
            j += 1
            power = 1
            if j < len(trace) and trace[j] == "^":
                j += 1
                k = j
                while k < len(trace) and trace[k].isdigit():
                    k += 1
                power = int(trace[j:k])
                j = k
            answer.append(("relator" if opening == "(" else "subgroup",
                           word * power))
            i = j
        else:
            assert opening.lower() in "xyz", (i, trace[i:])
            word = opening
            i += 1
            if i < len(trace) and trace[i] == "^":
                i += 1
                j = i
                while j < len(trace) and trace[j].isdigit():
                    j += 1
                word *= int(trace[i:j])
                i = j
            answer.append(("raw", word))
    return answer


RELATORS = [
    "xxx", "yyy", "zz", "xzxzxz", "yzyzyz",
    "XzxyXzxy", "YzyxYzyx", "xyxyxyxyxyxy",
]


def cyclic_forms(word):
    forms = set()
    for oriented in (word, inverse(word)):
        forms.update(oriented[i:] + oriented[:i] for i in range(len(oriented)))
    return forms


ITEMS = tokens(TRACE)
ALLOWED_RELATORS = set().union(*(cyclic_forms(r) for r in RELATORS))
for kind, word in ITEMS:
    if kind == "relator":
        assert word in ALLOWED_RELATORS, word
    elif kind == "subgroup":
        assert word in {"z", "Z", "xy", "YX"}, word

# PEACE `simp1`: erase delimiters but retain their contents.
SIMP1 = reduce_word("".join(word for _, word in ITEMS))
# PEACE `simp2`: erase relator items, retain subgroup items as bracketed
# atoms, and cancel only adjacent raw generator items.  In particular it does
# not expand a bracketed subgroup generator before performing cancellations.
simp2_chars = ""
for kind, word in ITEMS:
    if kind == "subgroup":
        simp2_chars += f"[{word}]"
    elif kind == "raw":
        for letter in word:
            if simp2_chars and simp2_chars[-1] == letter.swapcase():
                simp2_chars = simp2_chars[:-1]
            else:
                simp2_chars += letter
SIMP2 = simp2_chars

print(f"items={len(ITEMS)} relators={sum(k == 'relator' for k, _ in ITEMS)} "
      f"subgroup={sum(k == 'subgroup' for k, _ in ITEMS)}")
print(f"simp1={SIMP1!r}")
print(f"simp2={SIMP2!r}")

u = "z"
v = "xy"
expected_inner = u + v + u + inverse(v) + inverse(u) + v + inverse(u) \
    + inverse(v) + inverse(u) + inverse(v) + inverse(u) + v
expected = reduce_word(expected_inner * 2)
expanded_simp2 = reduce_word(SIMP2.replace("[", "").replace("]", ""))
print(f"expanded_simp2={expanded_simp2!r}")
print(f"expected={expected!r}")
assert SIMP1 == "y"
assert expanded_simp2 == expected

unique_relators = list(dict.fromkeys(word for kind, word in ITEMS
                                     if kind == "relator"))
print("relator forms:")
for index, word in enumerate(unique_relators):
    print(f"  r{index}={word}")

def lean_word(word):
    names = {"x": "X", "X": "X⁻¹", "y": "Y", "Y": "Y⁻¹",
             "z": "Z", "Z": "Z⁻¹"}
    return " * ".join(names[letter] for letter in word) or "1"

proof_items = []
for kind, word in ITEMS:
    if kind == "relator":
        proof_items.append(f"r{unique_relators.index(word)}")
    else:
        proof_items.append(f"({lean_word(word)})")
print("Lean proof word:")
print(" *\n    ".join(proof_items))
