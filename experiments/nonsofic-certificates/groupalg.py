"""Sparse arithmetic in the group algebra F_2[R^x], R = L_{F_2}(1,2).

An element is a finite set of units, keyed by the normal form of their values.
Coefficients are F_2, so adding a unit twice removes it.  In dual mode (see
leavitt.set_dual) every key is registered, which checks that no group element
reaches the algebra with two normal forms, and every unit product is
recomputed by prefix-table composition.
"""

from leavitt import Unit, ZERO, register_key, dual_enabled

__all__ = [
    "GroupAlgebraElement", "basis", "from_units", "matmul", "identity_matrix",
    "is_identity_matrix", "matrix_equal",
]


def _toggle_unit(support, unit):
    if dual_enabled():
        register_key(unit.val)
    key = unit.key
    if key in support:
        del support[key]
    else:
        support[key] = unit


class GroupAlgebraElement(object):
    __slots__ = ("_support",)

    def __init__(self, units=()):
        support = {}
        for unit in units:
            if not isinstance(unit, Unit):
                raise TypeError("group algebra elements are sums of Units")
            _toggle_unit(support, unit)
        self._support = support

    @classmethod
    def _wrap(cls, support):
        element = cls()
        element._support = support
        return element

    def support(self):
        return list(self._support.values())

    def keys(self):
        return set(self._support)

    def __len__(self):
        return len(self._support)

    def __add__(self, other):
        if not isinstance(other, GroupAlgebraElement):
            return NotImplemented
        support = dict(self._support)
        for unit in other._support.values():
            _toggle_unit(support, unit)
        return GroupAlgebraElement._wrap(support)

    __sub__ = __add__

    def __mul__(self, other):
        if not isinstance(other, GroupAlgebraElement):
            return NotImplemented
        support = {}
        right = list(other._support.values())
        for a in self._support.values():
            for b in right:
                _toggle_unit(support, a * b)
        return GroupAlgebraElement._wrap(support)

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("group algebra powers need a nonnegative integer exponent")
        result = one()
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base * base
        return result

    def is_zero(self):
        return not self._support

    def is_one(self):
        if len(self._support) != 1:
            return False
        (unit,) = self._support.values()
        return unit.is_identity()

    def augmentation(self):
        return len(self._support) % 2

    def evaluate(self):
        """The ring map pi: F_2[R^x] -> R, [u] -> u."""
        total = ZERO
        for unit in self._support.values():
            total = total + unit.val
        return total

    def star(self):
        """The canonical involution [u] -> [u^-1]."""
        return GroupAlgebraElement(unit.inverse() for unit in self._support.values())

    def __eq__(self, other):
        return isinstance(other, GroupAlgebraElement) and set(self._support) == set(other._support)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(frozenset(self._support))

    def __repr__(self):
        return "GroupAlgebraElement(support=%d)" % len(self._support)


def basis(unit):
    return GroupAlgebraElement([unit])


def from_units(units):
    return GroupAlgebraElement(units)


def one():
    from leavitt import IDENTITY
    return GroupAlgebraElement([IDENTITY])


def matmul(left, right):
    rows = len(left)
    inner = len(right)
    if any(len(row) != inner for row in left):
        raise ValueError("matrix shapes do not match")
    cols = len(right[0])
    out = []
    for i in range(rows):
        row = []
        for j in range(cols):
            acc = GroupAlgebraElement()
            for k in range(inner):
                if left[i][k].is_zero() or right[k][j].is_zero():
                    continue
                acc = acc + left[i][k] * right[k][j]
            row.append(acc)
        out.append(row)
    return out


def identity_matrix(d):
    return [[one() if i == j else GroupAlgebraElement() for j in range(d)] for i in range(d)]


def is_identity_matrix(matrix):
    d = len(matrix)
    for i in range(d):
        if len(matrix[i]) != d:
            return False
        for j in range(d):
            entry = matrix[i][j]
            if i == j:
                if not entry.is_one():
                    return False
            elif not entry.is_zero():
                return False
    return True


def matrix_equal(left, right):
    return len(left) == len(right) and all(
        len(a) == len(b) and all(x == y for x, y in zip(a, b)) for a, b in zip(left, right))
