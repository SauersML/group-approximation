#!/usr/bin/env python3
"""Certify that Q contains every even corner identity through length eight.

This MSI wrapper deliberately reuses the exact free-factor expansion and
moved-vector witnesses from the odd-girth classifier.  It screens only words
whose normal form in Q is nonempty.  Such a word is certified nontrivial in
the actual coefficient free product by a moved vector in every nonempty
free-factor syllable.
"""

from pathlib import Path


BASE = Path(__file__).with_name("classify-leavitt-odd-five-seven-corners.py")
source = BASE.read_text()
# Import definitions without running the base artifact's command-line census.
source = source.split("lengths = tuple(map(int, sys.argv[1:]))", 1)[0]
namespace = {"__file__": str(BASE), "__name__": "leavitt_corner_base"}
exec(compile(source, str(BASE), "exec"), namespace)


def q_reduce(word):
    """Free-product normal form in V4(h0,h2)*V4(k0,k1)*F(h1,k2)."""
    stack = []
    for name, sign in word:
        if name in ("h0", "h2", "k0", "k1"):
            factor = name[0].upper()
            value = 1 if name[1] == "0" else 2
            if stack and stack[-1][0] == factor:
                value ^= stack.pop()[1]
                if value:
                    stack.append((factor, value))
            else:
                stack.append((factor, value))
        else:
            item = (name, sign)
            if (stack and stack[-1][0] == "F"
                    and stack[-1][1:] == namespace["inverse"](item)):
                stack.pop()
            else:
                stack.append(("F", name, sign))
    return tuple(stack)


words = namespace["words"]
reduced_syllables = namespace["reduced_syllables"]
witnessed_nonidentity = namespace["witnessed_nonidentity"]

for length in (2, 4, 6, 8):
    total = 0
    q_nontrivial = 0
    certified = 0
    extra_identities = []
    unknown = []
    for word in words(length):
        total += 1
        if not q_reduce(word):
            continue
        q_nontrivial += 1
        blocks = reduced_syllables(word)
        if not blocks:
            extra_identities.append(word)
            continue
        unwitnessed = tuple(
            (copy, tokens) for copy, tokens in blocks
            if not witnessed_nonidentity(tokens)
        )
        if unwitnessed:
            unknown.append((word, unwitnessed))
        else:
            certified += 1
    print("LENGTH", length,
          "ORBIT_REPRESENTATIVES", total,
          "Q_NONTRIVIAL", q_nontrivial,
          "CERTIFIED_NONIDENTITIES", certified,
          "EXTRA_IDENTITIES", len(extra_identities),
          "UNKNOWNS", len(unknown), flush=True)
    for word in extra_identities[:20]:
        print("EXTRA", word)
    for word, blocks in unknown[:20]:
        print("UNKNOWN", word, blocks)
    assert not extra_identities
    assert not unknown
