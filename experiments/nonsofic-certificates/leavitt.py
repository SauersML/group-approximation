"""Exact arithmetic in the binary Leavitt algebra and its unit group.

    R = L_{F_2}(1,2) = F_2<s0, s1, t0, t1 | t_i s_j = delta_ij,  s0 t0 + s1 t1 = 1>,
    G = R^x.

Monomials.  A pair (alpha, beta) of binary words denotes

    S[alpha] T[beta] = s_{alpha_1} ... s_{alpha_k} t_{beta_l} ... t_{beta_1},

where T[beta] is the adjoint of S[beta] = s_{beta_1} ... s_{beta_l}.  Acting
on the F_2-span of infinite binary sequences, it replaces the prefix beta by
alpha: S[alpha]T[beta] e_{beta w} = e_{alpha w}, and it kills e_v when beta is
not a prefix of v.  This is the convention of
experiments/depth_one_paired_leavitt_return_search.py, whose `multiply`
selftest.py uses as a third implementation.

Path 1, normal form.  Orient t_i s_j -> delta_ij and s1 t1 -> 1 + s0 t0.  By
the Diamond lemma (research/leavitt-normal-form-decides-unit-words-proof.md),
the monomials with alpha and beta not both ending in "1" form an F_2-basis.  So
an element is a finite set of such pairs, and equality is set equality.

Path 2, prefix tables.  An element sends e_{u.T}, for a generic tail T, to a
finite F_2-sum of vectors e_{x.T}.  Record that sum on the leaves u of a
complete prefix code, then compose and add tables directly, and compare them
after merging sibling leaves.  R is simple, so this representation is faithful.
Path 2 never uses the rewriting rules.

After set_dual(True), every normal-form product is recomputed by table
composition and compared.  register_key() also checks that no element has two
normal forms.  Any disagreement raises PathDisagreement, which is always a bug
and never a mathematical answer.
"""

import re

__all__ = [
    "Elem", "OpTable", "Unit", "ParseError", "PathDisagreement",
    "ZERO", "ONE", "IDENTITY", "S", "T", "s0", "s1", "t0", "t1",
    "parse", "parse_elem", "parse_table", "elem_from_json", "render",
    "set_dual", "dual_enabled", "dual_stats", "register_key",
    "one_plus_nilpotent", "thompson_unit", "corner_matrix_unit",
    "is_complete_prefix_code", "psi2", "standard_units",
]


class PathDisagreement(AssertionError):
    """Normal form and prefix tables disagree: a bug, never an answer."""


class ParseError(ValueError):
    pass


_WORD_RE = re.compile(r"[01]*\Z")

_DUAL = {"on": False, "products": 0, "registered": 0, "parses": 0}
_REGISTRY = {}


def set_dual(flag=True):
    _DUAL["on"] = bool(flag)


def dual_enabled():
    return _DUAL["on"]


def dual_stats():
    return {
        "dual_mode": _DUAL["on"],
        "products_cross_checked": _DUAL["products"],
        "elements_registered": _DUAL["registered"],
        "parses_cross_checked": _DUAL["parses"],
    }


def _check_word(word):
    if not isinstance(word, str) or not _WORD_RE.match(word):
        raise ValueError("not a binary word: %r" % (word,))
    return word


def _toggle(bag, item):
    if item in bag:
        bag.remove(item)
    else:
        bag.add(item)


# ---------------------------------------------------------------------------
# Path 1: normal form


def _normalize_into(bag, alpha, beta):
    # S[x1]T[y1] = S[x]T[y] + S[x0]T[y0], repeated while both end in 1.
    while alpha.endswith("1") and beta.endswith("1"):
        alpha = alpha[:-1]
        beta = beta[:-1]
        _toggle(bag, (alpha + "0", beta + "0"))
    _toggle(bag, (alpha, beta))


def _multiply_terms(left, right):
    by_alpha = {}
    extensions = {}
    for c, d in right:
        by_alpha.setdefault(c, []).append(d)
        for i in range(len(c)):
            extensions.setdefault(c[:i], []).append((c, d))
    bag = set()
    for a, b in left:
        # T[b] S[c] with c a prefix of b (c == b included): T[rest], rest = b - c.
        for i in range(len(b) + 1):
            ds = by_alpha.get(b[:i])
            if ds:
                rest = b[i:]
                for d in ds:
                    _normalize_into(bag, a, d + rest)
        # T[b] S[c] with c strictly extending b: S[c - b].
        for c, d in extensions.get(b, ()):
            _normalize_into(bag, a + c[len(b):], d)
    return frozenset(bag)


class Elem(object):
    """An element of R, stored as its normal-form monomial set."""

    __slots__ = ("terms", "_key", "_table")

    def __init__(self, terms=frozenset()):
        # `terms` must already be a normal-form frozenset; use from_terms otherwise.
        self.terms = terms
        self._key = None
        self._table = None

    @classmethod
    def from_terms(cls, terms):
        bag = set()
        for pair in terms:
            alpha, beta = pair
            _normalize_into(bag, _check_word(alpha), _check_word(beta))
        return cls(frozenset(bag))

    @property
    def key(self):
        if self._key is None:
            self._key = tuple(sorted(self.terms))
        return self._key

    def table(self):
        if self._table is None:
            self._table = OpTable.from_terms(self.terms)
        return self._table

    def __add__(self, other):
        if not isinstance(other, Elem):
            return NotImplemented
        return Elem(self.terms ^ other.terms)

    __sub__ = __add__

    def __mul__(self, other):
        if not isinstance(other, Elem):
            return NotImplemented
        product = Elem(_multiply_terms(self.terms, other.terms))
        if _DUAL["on"]:
            composed = self.table().compose(other.table())
            if composed.canonical_key() != product.table().canonical_key():
                raise PathDisagreement(
                    "product disagrees between normal form and prefix tables: "
                    "(%s) * (%s)" % (render(self), render(other)))
            _DUAL["products"] += 1
        return product

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("ring powers need a nonnegative integer exponent")
        result = ONE
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base * base
        return result

    def star(self):
        return Elem(frozenset((b, a) for a, b in self.terms))

    def is_zero(self):
        return not self.terms

    def is_one(self):
        return self.terms == _ONE_TERMS

    def __eq__(self, other):
        return isinstance(other, Elem) and self.terms == other.terms

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.terms)

    def __len__(self):
        return len(self.terms)

    def __repr__(self):
        return "Elem(%s)" % render(self)

    def to_json(self):
        return [list(term) for term in self.key]


_ONE_TERMS = frozenset([("", "")])
ZERO = Elem(frozenset())
ONE = Elem(_ONE_TERMS)


def S(word):
    return Elem(frozenset([(_check_word(word), "")]))


def T(word):
    return Elem(frozenset([("", _check_word(word))]))


s0, s1, t0, t1 = S("0"), S("1"), T("0"), T("1")


def _render_monomial(alpha, beta):
    if not alpha and not beta:
        return "1"
    return ("S[%s]" % alpha if alpha else "") + ("T[%s]" % beta if beta else "")


def render(elem):
    if not elem.terms:
        return "0"
    return " + ".join(_render_monomial(a, b) for a, b in elem.key)


def register_key(elem):
    """Dual mode: check that this element's normal form is its only one."""
    if not _DUAL["on"]:
        return
    canonical = elem.table().canonical_key()
    prior = _REGISTRY.get(canonical)
    if prior is None:
        _REGISTRY[canonical] = elem.key
        _DUAL["registered"] += 1
    elif prior != elem.key:
        raise PathDisagreement(
            "one element with two normal forms: %r and %r" % (prior, elem.key))


# ---------------------------------------------------------------------------
# Path 2: prefix tables


class OpTable(object):
    """f e_{u.T} = sum of e_{x.T} over x in table[u], for leaves u of a complete prefix code."""

    __slots__ = ("table",)

    def __init__(self, table):
        self.table = table

    @classmethod
    def from_terms(cls, terms):
        by_beta = {}
        proper = set()
        for alpha, beta in terms:
            by_beta.setdefault(beta, []).append(alpha)
            for i in range(len(beta)):
                proper.add(beta[:i])
        table = {}
        stack = [""]
        while stack:
            u = stack.pop()
            if u in proper:
                stack.append(u + "0")
                stack.append(u + "1")
                continue
            bag = set()
            for i in range(len(u) + 1):
                alphas = by_beta.get(u[:i])
                if alphas:
                    rest = u[i:]
                    for alpha in alphas:
                        _toggle(bag, alpha + rest)
            table[u] = frozenset(bag)
        return cls(table)

    @classmethod
    def one(cls):
        return cls({"": frozenset([""])})

    @classmethod
    def zero(cls):
        return cls({"": frozenset()})

    @classmethod
    def S(cls, word):
        return cls({"": frozenset([_check_word(word)])})

    @classmethod
    def T(cls, word):
        word = _check_word(word)
        table = {word: frozenset([""])}
        for i in range(len(word)):
            sibling = word[:i] + ("1" if word[i] == "0" else "0")
            table[sibling] = frozenset()
        return cls(table)

    def evaluate(self, u):
        """Outputs on e_{u.T} if u extends a leaf, else None (u needs refining)."""
        table = self.table
        for i in range(len(u) + 1):
            outputs = table.get(u[:i])
            if outputs is not None:
                rest = u[i:]
                if not rest:
                    return outputs
                return frozenset(x + rest for x in outputs)
        return None

    def compose(self, other):
        """The table of self o other: apply other first, then self."""
        out = {}
        stack = list(other.table)
        while stack:
            u = stack.pop()
            inputs = other.evaluate(u)
            bag = set()
            refine = False
            for x in inputs:
                outputs = self.evaluate(x)
                if outputs is None:
                    refine = True
                    break
                for y in outputs:
                    _toggle(bag, y)
            if refine:
                stack.append(u + "0")
                stack.append(u + "1")
            else:
                out[u] = frozenset(bag)
        return OpTable(out)

    def __add__(self, other):
        out = {}
        stack = list(self.table)
        while stack:
            u = stack.pop()
            theirs = other.evaluate(u)
            if theirs is None:
                stack.append(u + "0")
                stack.append(u + "1")
                continue
            out[u] = self.evaluate(u) ^ theirs
        return OpTable(out)

    def canonical_key(self):
        table = dict(self.table)
        max_len = max(len(u) for u in table)
        for length in range(max_len, 0, -1):
            level = [u for u in table if len(u) == length and u[-1] == "0"]
            for u in level:
                sibling = u[:-1] + "1"
                if u not in table or sibling not in table:
                    continue
                zeros = table[u]
                ones = table[sibling]
                if len(zeros) != len(ones):
                    continue
                if any(not x.endswith("0") for x in zeros):
                    continue
                if any(not x.endswith("1") for x in ones):
                    continue
                parent = frozenset(x[:-1] for x in zeros)
                if parent != frozenset(x[:-1] for x in ones):
                    continue
                del table[u]
                del table[sibling]
                table[u[:-1]] = parent
        return tuple(sorted((u, tuple(sorted(xs))) for u, xs in table.items()))

    def equals(self, other):
        return self.canonical_key() == other.canonical_key()

    def is_one(self):
        return self.canonical_key() == (("", ("",)),)

    def is_zero(self):
        return self.canonical_key() == (("", ()),)


# ---------------------------------------------------------------------------
# Parsing:  S[01]T[10], s0 t1, 1 + s0 t1, (1+s0t1)(1+s1t0), (s0+t1)^3


_TOKEN_RE = re.compile(
    r"(?P<S>S\[[01]*\])|(?P<T>T\[[01]*\])|(?P<st>[st][01])|(?P<int>\d+)|(?P<op>[+*^()])")


def _tokenize(text):
    if not isinstance(text, str):
        raise ParseError("expression must be a string, got %r" % (text,))
    tokens = []
    pos = 0
    n = len(text)
    while True:
        while pos < n and text[pos].isspace():
            pos += 1
        if pos >= n:
            return tokens
        match = _TOKEN_RE.match(text, pos)
        if match is None:
            raise ParseError("cannot read %r at position %d" % (text[pos:pos + 12], pos))
        if match.group("S") is not None:
            tokens.append(("S", match.group("S")[2:-1]))
        elif match.group("T") is not None:
            tokens.append(("T", match.group("T")[2:-1]))
        elif match.group("st") is not None:
            if match.end() < n and text[match.end()].isdigit():
                raise ParseError(
                    "ambiguous %r: write S[..]/T[..] or separate the letters"
                    % text[pos:match.end() + 1])
            letter, bit = match.group("st")
            tokens.append(("S" if letter == "s" else "T", bit))
        elif match.group("int") is not None:
            tokens.append(("int", int(match.group("int"))))
        else:
            tokens.append(("op", match.group("op")))
        pos = match.end()


def parse(text):
    """Parse a ring expression into an n-ary syntax tree."""
    tokens = _tokenize(text)
    state = [0]

    def peek():
        return tokens[state[0]] if state[0] < len(tokens) else None

    def take():
        token = peek()
        if token is None:
            raise ParseError("unexpected end of expression %r" % (text,))
        state[0] += 1
        return token

    def expression():
        terms = [product()]
        while peek() == ("op", "+"):
            take()
            terms.append(product())
        return terms[0] if len(terms) == 1 else ("sum", terms)

    def starts_atom(token):
        return token is not None and (token[0] in ("S", "T", "int") or token == ("op", "("))

    def product():
        factors = [power()]
        while True:
            token = peek()
            if token == ("op", "*"):
                take()
                factors.append(power())
            elif starts_atom(token):
                factors.append(power())
            else:
                break
        return factors[0] if len(factors) == 1 else ("prod", factors)

    def power():
        node = atom()
        while peek() == ("op", "^"):
            take()
            token = take()
            if token[0] != "int":
                raise ParseError("exponent must be a nonnegative integer")
            node = ("pow", node, token[1])
        return node

    def atom():
        token = take()
        if token == ("op", "("):
            node = expression()
            if take() != ("op", ")"):
                raise ParseError("missing closing parenthesis in %r" % (text,))
            return node
        if token[0] in ("S", "T"):
            return (token[0], token[1])
        if token[0] == "int":
            if token[1] in (0, 1):
                return ("const", token[1])
            raise ParseError("the only constants are 0 and 1")
        raise ParseError("unexpected token %r in %r" % (token, text))

    node = expression()
    if peek() is not None:
        raise ParseError("unexpected trailing token %r in %r" % (peek(), text))
    return node


class _ElemBackend(object):
    zero = staticmethod(lambda: ZERO)
    one = staticmethod(lambda: ONE)
    S = staticmethod(S)
    T = staticmethod(T)
    add = staticmethod(lambda a, b: a + b)
    mul = staticmethod(lambda a, b: a * b)


class _TableBackend(object):
    zero = staticmethod(OpTable.zero)
    one = staticmethod(OpTable.one)
    S = staticmethod(OpTable.S)
    T = staticmethod(OpTable.T)
    add = staticmethod(lambda a, b: a + b)
    mul = staticmethod(lambda a, b: a.compose(b))


def evaluate(node, backend):
    kind = node[0]
    if kind == "const":
        return backend.one() if node[1] else backend.zero()
    if kind == "S":
        return backend.S(node[1])
    if kind == "T":
        return backend.T(node[1])
    if kind == "sum":
        acc = backend.zero()
        for child in node[1]:
            acc = backend.add(acc, evaluate(child, backend))
        return acc
    if kind == "prod":
        acc = backend.one()
        for child in node[1]:
            acc = backend.mul(acc, evaluate(child, backend))
        return acc
    if kind == "pow":
        base = evaluate(node[1], backend)
        acc = backend.one()
        for _ in range(node[2]):
            acc = backend.mul(acc, base)
        return acc
    raise ParseError("bad syntax node %r" % (kind,))


def parse_elem(text):
    node = parse(text)
    elem = evaluate(node, _ElemBackend)
    if _DUAL["on"]:
        table = evaluate(node, _TableBackend)
        if table.canonical_key() != elem.table().canonical_key():
            raise PathDisagreement("parse disagrees between paths: %r" % (text,))
        _DUAL["parses"] += 1
    return elem


def parse_table(text):
    return evaluate(parse(text), _TableBackend)


def elem_from_json(value):
    """A string expression, or a list of [alpha, beta] monomials."""
    if isinstance(value, str):
        return parse_elem(value)
    if isinstance(value, list):
        return Elem.from_terms(tuple(pair) for pair in value)
    raise ParseError("ring element must be an expression string or a monomial list")


# ---------------------------------------------------------------------------
# Units


class Unit(object):
    """A unit of R carried with its inverse; equality is equality of values."""

    __slots__ = ("val", "_inv", "_parts")

    def __init__(self, val, inv=None, check=True, _parts=None):
        if not isinstance(val, Elem):
            raise TypeError("Unit value must be an Elem")
        if inv is None and _parts is None:
            raise ValueError("a unit needs its inverse")
        if check:
            if inv is None:
                raise ValueError("cannot check a unit without an explicit inverse")
            if not (val * inv).is_one():
                raise ValueError("val * inv != 1 for val = %s" % render(val))
            if not (inv * val).is_one():
                raise ValueError("inv * val != 1 for val = %s" % render(val))
        self.val = val
        self._inv = inv
        self._parts = _parts

    @property
    def inv(self):
        if self._inv is None:
            stack = [self]
            while stack:
                node = stack[-1]
                if node._inv is not None:
                    stack.pop()
                    continue
                left, right = node._parts
                pending = [part for part in (left, right) if part._inv is None]
                if pending:
                    stack.extend(pending)
                    continue
                node._inv = right._inv * left._inv
                node._parts = None
                stack.pop()
        return self._inv

    @property
    def key(self):
        return self.val.key

    def __mul__(self, other):
        if not isinstance(other, Unit):
            return NotImplemented
        return Unit(self.val * other.val, None, check=False, _parts=(self, other))

    def inverse(self):
        return Unit(self.inv, self.val, check=False)

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise ValueError("unit powers need an integer exponent")
        base = self
        if exponent < 0:
            base = self.inverse()
            exponent = -exponent
        result = IDENTITY
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base * base
        return result

    def is_identity(self):
        return self.val.is_one()

    def order(self, limit=64):
        power = self
        for n in range(1, limit + 1):
            if power.is_identity():
                return n
            power = power * self
        return None

    def __eq__(self, other):
        return isinstance(other, Unit) and self.val.terms == other.val.terms

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.val.terms)

    def __repr__(self):
        return "Unit(%s)" % render(self.val)


IDENTITY = Unit(ONE, ONE, check=False)


def one_plus_nilpotent(n, max_power=256):
    """The unit 1 + n for nilpotent n, with inverse 1 + n + ... + n^(k-1)."""
    inverse = ONE
    power = ONE
    for _ in range(max_power):
        power = power * n
        if power.is_zero():
            return Unit(ONE + n, inverse)
        inverse = inverse + power
    raise ValueError("element is not nilpotent within %d powers" % max_power)


def is_complete_prefix_code(words):
    words = [_check_word(w) for w in words]
    if not words:
        return False
    for i, a in enumerate(words):
        for b in words[i + 1:]:
            if a.startswith(b) or b.startswith(a):
                return False
    depth = max(len(w) for w in words)
    return sum(1 << (depth - len(w)) for w in words) == 1 << depth


def thompson_unit(domain, range_words):
    """The Thompson-V unit sending domain[i] w to range[i] w (two complete prefix codes)."""
    domain = list(domain)
    range_words = list(range_words)
    if len(domain) != len(range_words):
        raise ValueError("prefix codes of different sizes")
    if not is_complete_prefix_code(domain) or not is_complete_prefix_code(range_words):
        raise ValueError("thompson_unit needs two complete prefix codes")
    val = Elem.from_terms(zip(range_words, domain))
    inv = Elem.from_terms(zip(domain, range_words))
    return Unit(val, inv)


def _gf2_inverse_columns(columns, n):
    rows = [0] * n
    for j, column in enumerate(columns):
        for i in range(n):
            if (column >> i) & 1:
                rows[i] |= 1 << j
    augmented = [rows[i] | (1 << (n + i)) for i in range(n)]
    for c in range(n):
        pivot = None
        for r in range(c, n):
            if (augmented[r] >> c) & 1:
                pivot = r
                break
        if pivot is None:
            raise ValueError("matrix is singular over F_2")
        augmented[c], augmented[pivot] = augmented[pivot], augmented[c]
        for r in range(n):
            if r != c and (augmented[r] >> c) & 1:
                augmented[r] ^= augmented[c]
    inverse_rows = [augmented[i] >> n for i in range(n)]
    inverse_columns = [0] * n
    for i in range(n):
        for j in range(n):
            if (inverse_rows[i] >> j) & 1:
                inverse_columns[j] |= 1 << i
    return inverse_columns


def corner_matrix_unit(leaves, columns):
    """sum_{i,j} M_ij S[leaf_i]T[leaf_j] + (1 - sum_i S[leaf_i]T[leaf_i]).

    `columns[j]` is a bitset whose bit i is M_ij (the column convention of
    experiments/kaplansky_finite_drazin_seed.py and of the atlas charts).
    """
    leaves = [_check_word(leaf) for leaf in leaves]
    n = len(leaves)
    columns = [int(c) for c in columns]
    if len(columns) != n:
        raise ValueError("need one column per leaf")
    for i in range(n):
        for j in range(i + 1, n):
            if leaves[i].startswith(leaves[j]) or leaves[j].startswith(leaves[i]):
                raise ValueError("leaves must be pairwise prefix-incomparable")
    for column in columns:
        if column < 0 or column >> n:
            raise ValueError("column bitset out of range")
    inverse_columns = _gf2_inverse_columns(columns, n)
    complement = ONE + Elem.from_terms((leaf, leaf) for leaf in leaves)

    def block(cols):
        return Elem.from_terms(
            (leaves[i], leaves[j]) for j in range(n) for i in range(n) if (cols[j] >> i) & 1)

    return Unit(block(columns) + complement, block(inverse_columns) + complement)


def psi2(a, b, c, d):
    """The self-similarity M_2(R) -> R:  [[a,b],[c,d]] -> s0 a t0 + s0 b t1 + s1 c t0 + s1 d t1."""
    return s0 * a * t0 + s0 * b * t1 + s1 * c * t0 + s1 * d * t1


def standard_units():
    """x = s0t1, y = s1t0; u = 1+x, v = 1+y, w = x+y are involutions and g = uv has order three."""
    x = s0 * t1
    y = s1 * t0
    u = Unit(ONE + x, ONE + x)
    v = Unit(ONE + y, ONE + y)
    w = Unit(x + y, x + y)
    g = u * v
    g_inverse = v * u
    return {
        "@e": IDENTITY,
        "@u": u,
        "@v": v,
        "@w": w,
        "@g": Unit(g.val, g_inverse.val),
    }
