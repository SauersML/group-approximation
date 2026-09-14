#!/usr/bin/env python3
"""Exact arithmetic in the ternary Leavitt algebra, its unit group, and the anti-central summand.

    R = L_{F_3}(1,2) = F_3<s0, s1, t0, t1 | t_i s_j = delta_ij,  s0 t0 + s1 t1 = 1>,
    G = R^x,   z = -1 (central, order two),
    S_- = eps_- F_3[G] = F_3[G] / (1 + [z]),   eps_- = 2(1 - [z]).

Path 1, normal form. S[alpha]T[beta] = s_{alpha_1}..s_{alpha_k} t_{beta_l}..t_{beta_1}. Orient
s1 t1 -> 1 - s0 t0, so S[x1]T[y1] = S[x]T[y] - S[x0]T[y0]; the monomials with alpha, beta not
both ending in "1" span R (the F_3 analogue of the binary diamond-lemma basis). An element is a
dict {(alpha, beta): c} with c in {1, 2}.

Path 2, operator action. S[alpha]T[beta] sends e_{beta v . tail} to e_{alpha v . tail} (generic
tail) and kills e_u when beta is not a prefix of u. set_dual(True) recomputes every product by
composing actions on all words of a common length and compares. A disagreement raises
PathDisagreement, which is a bug, never an answer. R is simple, so this action is faithful.

The anti-central group algebra stores [g] under a signed canonical key: of g and -g = zg, the one
whose first sorted monomial has coefficient 1, with the sign moved to the coefficient. This is
exactly F_3[G]/(1 + [z]). Pure Python 3.8, stdlib only.
"""

import itertools

P = 3
_DUAL = {"on": False, "checked": 0}


class PathDisagreement(AssertionError):
    pass


def set_dual(flag=True):
    _DUAL["on"] = bool(flag)


def dual_stats():
    return dict(_DUAL)


def _add(bag, key, c):
    v = (bag.get(key, 0) + c) % P
    if v:
        bag[key] = v
    else:
        bag.pop(key, None)


def _normalize_into(bag, alpha, beta, c):
    c %= P
    if not c:
        return
    while alpha.endswith("1") and beta.endswith("1"):
        alpha, beta = alpha[:-1], beta[:-1]
        _add(bag, (alpha + "0", beta + "0"), -c)
    _add(bag, (alpha, beta), c)


def elem(terms):
    """Normalize an iterable of ((alpha, beta), coefficient)."""
    bag = {}
    for (a, b), c in terms:
        if set(a) - {"0", "1"} or set(b) - {"0", "1"}:
            raise ValueError("not binary words: %r %r" % (a, b))
        _normalize_into(bag, a, b, c)
    return bag


def add(x, y, cy=1):
    out = dict(x)
    for k, c in y.items():
        _add(out, k, cy * c)
    return out


def scale(x, c):
    return {k: (v * c) % P for k, v in x.items() if (v * c) % P}


def _mul_raw(left, right):
    by_alpha, ext = {}, {}
    for (c, d), k in right.items():
        by_alpha.setdefault(c, []).append((d, k))
        for i in range(len(c)):
            ext.setdefault(c[:i], []).append((c, d, k))
    bag = {}
    for (a, b), k1 in left.items():
        for i in range(len(b) + 1):          # T[b] S[b[:i]] = T[b[i:]]
            for d, k2 in by_alpha.get(b[:i], ()):
                _normalize_into(bag, a, d + b[i:], k1 * k2)
        for c, d, k2 in ext.get(b, ()):      # T[b] S[b mu] = S[mu]
            _normalize_into(bag, a + c[len(b):], d, k1 * k2)
    return bag


def _maxbeta(x):
    return max((len(b) for (_, b) in x), default=0)


def act(x, word):
    """Path 2: x applied to e_{word . tail}; needs len(word) >= every beta of x."""
    out = {}
    for (a, b), k in x.items():
        if len(word) < len(b):
            raise ValueError("word shorter than a beta")
        if word.startswith(b):
            _add(out, a + word[len(b):], k)
    return out


def act_compose_equal(x, y, xy):
    L = _maxbeta(x) + _maxbeta(y)
    L = max(L, _maxbeta(xy))
    for bits in itertools.product("01", repeat=L):
        u = "".join(bits)
        mid = act(y, u)
        via = {}
        for v, c in mid.items():
            for w2, c2 in act(x, v).items():
                _add(via, w2, c * c2)
        if via != act(xy, u):
            return False
    return True


def mul(x, y):
    prod = _mul_raw(x, y)
    if _DUAL["on"]:
        if not act_compose_equal(x, y, prod):
            raise PathDisagreement("product disagrees between normal form and action")
        _DUAL["checked"] += 1
    return prod


def key(x):
    return tuple(sorted(x.items()))


def is_one(x):
    return x == {("", ""): 1}


ONE = {("", ""): 1}
MINUS_ONE = {("", ""): 2}


def S(word):
    return elem([((word, ""), 1)])


def T(word):
    return elem([(("", word), 1)])


s0, s1, t0, t1 = S("0"), S("1"), T("0"), T("1")


def render(x):
    if not x:
        return "0"
    parts = []
    for (a, b), c in sorted(x.items()):
        mono = ("S[%s]" % a if a else "") + ("T[%s]" % b if b else "") or "1"
        parts.append(("" if c == 1 else "2*") + mono)
    return " + ".join(parts)


class Unit(object):
    """A unit of R with a checked inverse."""

    __slots__ = ("val", "inv")

    def __init__(self, val, inv, check=True):
        if check and not (is_one(mul(val, inv)) and is_one(mul(inv, val))):
            raise ValueError("not an inverse pair: %s" % render(val))
        self.val, self.inv = val, inv

    def __mul__(self, other):
        return Unit(mul(self.val, other.val), mul(other.inv, self.inv), check=False)

    def inverse(self):
        return Unit(self.inv, self.val, check=False)

    def signed(self):
        """(canonical unit, sign) with self = sign * canonical, sign in {1, 2}."""
        k = key(self.val)
        if k[0][1] == 1:
            return self, 1
        return Unit(scale(self.val, 2), scale(self.inv, 2), check=False), 2


IDENTITY = Unit(ONE, ONE)
Z = Unit(MINUS_ONE, MINUS_ONE)


def one_plus_nilpotent(n, cap=64):
    """1 + n and its inverse sum (-n)^k, for nilpotent n."""
    inv, power, sign = dict(ONE), dict(ONE), 1
    for _ in range(cap):
        power = mul(power, n)
        if not power:
            return Unit(add(ONE, n), inv)
        sign = -sign
        inv = add(inv, power, sign)
    raise ValueError("not nilpotent within cap")


def thompson_unit(domain, range_):
    """Sends the prefix domain[i] to range_[i]; both must be complete prefix codes."""
    val = elem([((r, d), 1) for d, r in zip(domain, range_)])
    inv = elem([((d, r), 1) for d, r in zip(domain, range_)])
    return Unit(val, inv)


def diagonal_unit(leaves, signs):
    val = elem([((g, g), s) for g, s in zip(leaves, signs)])
    return Unit(val, val)


W = Unit(add(mul(s0, t1), mul(s1, t0)), add(mul(s0, t1), mul(s1, t0)))
D = diagonal_unit(["0", "1"], [1, 2])


class SMinus(object):
    """Anti-central group algebra S_- = F_3[G]/(1 + [z]) over a shared unit registry."""

    def __init__(self):
        self.units = {}
        self.cache = {}

    def basis(self, u):
        can, sign = u.signed()
        k = key(can.val)
        self.units.setdefault(k, can)
        return k, sign

    def of_unit(self, u, c=1):
        k, sign = self.basis(u)
        return {k: (c * sign) % P}

    def mul_keys(self, k1, k2):
        hit = self.cache.get((k1, k2))
        if hit is None:
            hit = self.basis(self.units[k1] * self.units[k2])
            self.cache[(k1, k2)] = hit
        return hit

    def mul(self, x, y):
        out = {}
        for k1, c1 in x.items():
            for k2, c2 in y.items():
                k, sign = self.mul_keys(k1, k2)
                _add(out, k, c1 * c2 * sign)
        return out

    def evaluate(self, x):
        """pi : S_- -> R, [g] -> g."""
        out = {}
        for k, c in x.items():
            out = add(out, self.units[k].val, c)
        return out

    def one(self):
        return self.of_unit(IDENTITY)
