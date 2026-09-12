"""Normal-closure derivations in the free product R^x * <x>.

A word is a list of syllables ("u", Unit) or ("x", n).  reduce_word()
multiplies adjacent units, adds adjacent exponents and drops trivial
syllables.  The result is the free-product normal form: an alternating list of
nontrivial syllables, which is trivial exactly when empty (the word problem of
R^x is solved by the normal form of R).

A certificate that c lies in the normal closure of w is a finite list of
pairs (h_j, e_j), with h_j words and e_j nonzero integers, such that

    c = prod_j h_j w^{e_j} h_j^{-1}          in R^x * <x>.

If c != 1 and the exponent sum of x in w is nonzero, then w has no solution in
any group containing R^x.  A solution z would give a homomorphism
R^x * <x> -> K that is the identity on R^x and sends w, hence c, to 1.  So w
violates the Kervaire--Laudenbach conjecture over R^x, and R^x is not
hyperlinear, because KL holds for hyperlinear groups (Nitsche--Thom,
arXiv:1811.07737, Theorem 1.3).
"""

from leavitt import Unit

__all__ = ["reduce_word", "extend_reduced", "invert_word", "exponent_sum",
           "word_power", "verify_normal_closure"]


def extend_reduced(stack, syllables):
    """Append syllables to an already reduced word, in place."""
    for kind, value in syllables:
        if kind == "x":
            if not isinstance(value, int):
                raise ValueError("x exponents must be integers")
            if value == 0:
                continue
        elif kind == "u":
            if not isinstance(value, Unit):
                raise TypeError("unit syllables must carry Units")
            if value.is_identity():
                continue
        else:
            raise ValueError("unknown syllable kind %r" % (kind,))
        if stack and stack[-1][0] == kind:
            _, previous = stack.pop()
            merged = previous + value if kind == "x" else previous * value
            trivial = merged == 0 if kind == "x" else merged.is_identity()
            if not trivial:
                stack.append((kind, merged))
        else:
            stack.append((kind, value))
    return stack


def reduce_word(syllables):
    return extend_reduced([], syllables)


def invert_word(syllables):
    out = []
    for kind, value in reversed(list(syllables)):
        out.append((kind, -value) if kind == "x" else (kind, value.inverse()))
    return out


def exponent_sum(syllables):
    return sum(value for kind, value in syllables if kind == "x")


def word_power(syllables, exponent):
    base = list(syllables) if exponent > 0 else invert_word(syllables)
    return base * abs(exponent)


def verify_normal_closure(coefficient, equation, factors, require_nonsingular=True):
    """Check c = prod h_j w^{e_j} h_j^-1 step by step.

    Returns (passed, report).  The report records the exponent sum, the reduced
    length after each factor, and the final reduced word length.
    """
    report = {"exponent_sum": exponent_sum(equation), "step_lengths": [], "reasons": []}
    passed = True
    if require_nonsingular and report["exponent_sum"] == 0:
        passed = False
        report["reasons"].append("the equation is singular: exponent sum of x is 0")
    if coefficient.is_identity():
        passed = False
        report["reasons"].append("the coefficient is the identity")
    w = reduce_word(equation)
    accumulated = []
    for conjugator, exponent in factors:
        if not isinstance(exponent, int) or exponent == 0:
            raise ValueError("factor exponents must be nonzero integers")
        h = reduce_word(conjugator)
        extend_reduced(accumulated, h)
        extend_reduced(accumulated, word_power(w, exponent))
        extend_reduced(accumulated, invert_word(h))
        report["step_lengths"].append(len(accumulated))
    report["final_length"] = len(accumulated)
    matches = (len(accumulated) == 1 and accumulated[0][0] == "u"
               and accumulated[0][1] == coefficient)
    if not matches:
        passed = False
        report["reasons"].append(
            "the product of conjugates reduces to a word of length %d, not to the coefficient"
            % len(accumulated))
    return passed, report
