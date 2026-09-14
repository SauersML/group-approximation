"""Exact arithmetic in Thompson's group V (prefix-code permutations of Cantor space).

An element is stored as a canonical list of pairs (domain prefix, range prefix)
forming complete prefix codes, reduced by removing carets.  Elements act on the
RIGHT, matching the Bleak--Quick convention used on main
(`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`): for words,
x*y means "first x, then y".

Generators (Bleak--Quick, as quoted on main):
  a = (00 01)            swap cones 00 and 01
  b = (01 10 11)         cycle cones 01 -> 10 -> 11 -> 01
  c = (1 00)             swap cones 1 and 00 (cone 01 fixed)
"""

from itertools import product


def _complete_split(code):
    return code


class V:
    __slots__ = ("pairs",)

    def __init__(self, pairs):
        # pairs: dict domain_prefix -> range_prefix ; complete prefix codes
        self.pairs = _reduce(dict(pairs))

    def __eq__(self, other):
        return self.pairs == other.pairs

    def __hash__(self):
        return hash(tuple(sorted(self.pairs.items())))

    def key(self):
        return tuple(sorted(self.pairs.items()))

    def apply(self, s):
        # s: binary string long enough to have a prefix in the domain code
        for d, r in self.pairs.items():
            if s.startswith(d):
                return r + s[len(d):]
        raise ValueError("string too short for this element: " + s)

    def inverse(self):
        return V({r: d for d, r in self.pairs.items()})

    def __mul__(self, other):
        # right action: first self, then other
        out = {}
        stack = list(self.pairs.items())
        while stack:
            d, r = stack.pop()
            # find other's domain prefix compatible with r
            hit = None
            for d2, r2 in other.pairs.items():
                if r.startswith(d2):
                    hit = (d2, r2)
                    break
                if d2.startswith(r):
                    hit = None
                    # r is a proper prefix of some d2: split this pair
                    stack.append((d + "0", r + "0"))
                    stack.append((d + "1", r + "1"))
                    break
            else:
                raise AssertionError("incomplete code")
            if hit is not None:
                d2, r2 = hit
                out[d] = r2 + r[len(d2):]
        return V(out)

    def order_bound(self, bound=50):
        x = self
        e = identity()
        for k in range(1, bound + 1):
            if x == e:
                return k
            x = x * self
        return None


def _reduce(pairs):
    # remove carets: if d0->r0 and d1->r1 with r0=r+"0", r1=r+"1", merge to d->r
    changed = True
    while changed:
        changed = False
        for d in list(pairs.keys()):
            if not d or d not in pairs:
                continue
            if d.endswith("0"):
                sib = d[:-1] + "1"
                if sib in pairs:
                    r0, r1 = pairs[d], pairs[sib]
                    if r0 and r1 and r0[:-1] == r1[:-1] and r0.endswith("0") and r1.endswith("1"):
                        p = d[:-1]
                        del pairs[d]
                        del pairs[sib]
                        pairs[p] = r0[:-1]
                        changed = True
    return pairs


def identity():
    return V({"": ""})


def gen_a():
    return V({"00": "01", "01": "00", "1": "1"})


def gen_b():
    return V({"00": "00", "01": "10", "10": "11", "11": "01"})


def gen_c():
    return V({"1": "00", "00": "1", "01": "01"})


GENS = {"a": gen_a(), "b": gen_b(), "c": gen_c()}
GENS["A"] = GENS["a"].inverse()
GENS["B"] = GENS["b"].inverse()
GENS["C"] = GENS["c"].inverse()


def word(w):
    x = identity()
    for ch in w:
        x = x * GENS[ch]
    return x


BQ_RELATORS = {
    # Bleak--Quick (2.4) as quoted on main in
    # research/thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3.md ; B = b^-1
    "a^2": "aa", "b^3": "bbb", "(ab)^4": "abababab", "c^2": "cc", "(ac)^3": "acacac",
    "r5": "caBaba" * 2 + "cb" + "cabaBa" * 2,
    "r6": "a" + "cb" * 2 + "a" + "Bc" * 2 + "bcabcBcaBacB" + "cb" * 2 + "aB",
    "r7": "aBcbc" + "aB" * 2 + "cbcBa" + "Bc" * 2 + "babcBcaB",
    "r8": "ca" + "Bc" * 2 + "bacabacbc" + "Bca" * 2 + "b" + "cB" * 2 + "acb" * 2 + "cBcaB",
}


def check_bleak_quick(reverse=False):
    """Verify the nine Bleak--Quick relators hold for the exact generators.

    reverse=True reads every word right to left (left-action convention)."""
    e = identity()
    return {k: (word(v[::-1] if reverse else v) == e) for k, v in BQ_RELATORS.items()}


if __name__ == "__main__":
    print("right-action reading:", check_bleak_quick(False))
    print("left-action reading: ", check_bleak_quick(True))
    print("orders a,b,c:", GENS["a"].order_bound(), GENS["b"].order_bound(), GENS["c"].order_bound())
