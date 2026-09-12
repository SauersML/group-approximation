"""Cellular automata over A^G with G = R^x, R = L_{F_2}(1,2).

Convention.  Alphabet A = {0, ..., k-1}.  An automaton has a finite memory
list M = (m_0, ..., m_{r-1}) of distinct units and a local rule
mu: A^M -> A, stored as a table of k^r symbols.  A pattern p gets the index
sum_i p_i k^i (m_0 is the least significant digit), and

    tau(x)(g) = mu( x(g m_0), ..., x(g m_{r-1}) ).

This is G-equivariant for (h.x)(g) = x(h^-1 g).  Composition (sigma o tau) has
memory N.M = {n m}.  The linear automaton of a in F_2[G],
tau_a(x)(g) = sum_{h in supp a} x(g h), satisfies tau_a o tau_b = tau_{ab}.

Exact tests:
  * compose_is_identity(sigma, tau): sigma o tau = id, checked on every pattern
    over N.M (any pattern extends to a configuration, so this is complete);
  * garden_of_eden(tau, cells, values): exhaustive backtracking over the
    variables Omega.M; True means no configuration x has tau(x) = values on
    the cells, so tau is not surjective.

sigma o tau = id proves tau injective.  Together with one Garden-of-Eden
pattern it proves tau injective and not surjective, which refutes Gottschalk's
conjecture for G.
"""

from leavitt import Unit, IDENTITY

__all__ = [
    "CellularAutomaton", "compose", "compose_is_identity", "equal",
    "is_identity", "garden_of_eden", "linear_automaton", "shift_automaton",
]


def _iterate_patterns(k, length):
    """Yield (index, digits); `digits` is one list mutated in place."""
    digits = [0] * length
    for index in range(k ** length):
        yield index, digits
        for j in range(length):
            digits[j] += 1
            if digits[j] < k:
                break
            digits[j] = 0


class CellularAutomaton(object):
    __slots__ = ("k", "memory", "rule", "index")

    def __init__(self, alphabet, memory, rule):
        k = int(alphabet)
        if k < 1:
            raise ValueError("alphabet must be nonempty")
        memory = list(memory)
        index = {}
        for i, unit in enumerate(memory):
            if not isinstance(unit, Unit):
                raise TypeError("memory elements must be Units")
            if unit.key in index:
                raise ValueError("memory elements must be distinct")
            index[unit.key] = i
        rule = list(rule)
        size = k ** len(memory)
        if len(rule) != size:
            raise ValueError("rule has %d entries; k^|M| = %d" % (len(rule), size))
        for symbol in rule:
            if not isinstance(symbol, int) or not 0 <= symbol < k:
                raise ValueError("rule symbols must be integers in [0, %d)" % k)
        self.k = k
        self.memory = memory
        self.rule = bytes(rule) if k <= 256 else tuple(rule)
        self.index = index

    def local(self, digits):
        k = self.k
        position = 0
        scale = 1
        for digit in digits:
            position += digit * scale
            scale *= k
        return self.rule[position]


def shift_automaton(k, h):
    """tau(x)(g) = x(g h); its inverse is the shift by h^-1."""
    return CellularAutomaton(k, [h], list(range(k)))


def linear_automaton(element):
    """tau_a(x)(g) = sum_{h in supp a} x(g h) over F_2."""
    memory = sorted(element.support(), key=lambda unit: unit.key)
    rule = [bin(i).count("1") & 1 for i in range(2 ** len(memory))]
    return CellularAutomaton(2, memory, rule)


def _product_memory(sigma, tau):
    memory = []
    index = {}
    positions = []
    for n in sigma.memory:
        row = []
        for m in tau.memory:
            product = n * m
            key = product.key
            if key not in index:
                index[key] = len(memory)
                memory.append(product)
            row.append(index[key])
        positions.append(row)
    return memory, index, positions


def _composite_values(sigma, tau, positions, digits, powers):
    k = sigma.k
    outer = 0
    scale = 1
    rule = tau.rule
    for row in positions:
        position = 0
        for j, p in enumerate(row):
            position += digits[p] * powers[j]
        outer += rule[position] * scale
        scale *= k
    return sigma.rule[outer]


def compose(sigma, tau, limit=1 << 22):
    """The automaton sigma o tau, as a full table over N.M."""
    if sigma.k != tau.k:
        raise ValueError("alphabets differ")
    k = sigma.k
    memory, _, positions = _product_memory(sigma, tau)
    size = k ** len(memory)
    if size > limit:
        raise ValueError("composite table has %d entries (limit %d)" % (size, limit))
    powers = [k ** j for j in range(len(tau.memory))]
    table = bytearray(size)
    for index, digits in _iterate_patterns(k, len(memory)):
        table[index] = _composite_values(sigma, tau, positions, digits, powers)
    return CellularAutomaton(k, memory, list(table))


def compose_is_identity(sigma, tau, limit=1 << 30):
    """Return (True, None) iff sigma o tau is the identity; else (False, counterexample)."""
    if sigma.k != tau.k:
        raise ValueError("alphabets differ")
    k = sigma.k
    memory, index, positions = _product_memory(sigma, tau)
    if IDENTITY.key not in index:
        return False, {"reason": "the identity is not in the composite memory N.M"}
    e = index[IDENTITY.key]
    size = k ** len(memory)
    if size > limit:
        raise ValueError("composite has %d patterns (limit %d)" % (size, limit))
    powers = [k ** j for j in range(len(tau.memory))]
    for position, digits in _iterate_patterns(k, len(memory)):
        if _composite_values(sigma, tau, positions, digits, powers) != digits[e]:
            return False, {"reason": "composite differs from identity",
                           "pattern_index": position, "memory_size": len(memory)}
    return True, {"patterns_checked": size, "memory_size": len(memory)}


def is_identity(automaton):
    e = automaton.index.get(IDENTITY.key)
    if e is None:
        return False
    for position, digits in _iterate_patterns(automaton.k, len(automaton.memory)):
        if automaton.rule[position] != digits[e]:
            return False
    return True


def equal(first, second, limit=1 << 24):
    """Equality of automata, checked on every pattern over the union of memories."""
    if first.k != second.k:
        return False
    union = []
    index = {}
    for unit in list(first.memory) + list(second.memory):
        if unit.key not in index:
            index[unit.key] = len(union)
            union.append(unit)
    size = first.k ** len(union)
    if size > limit:
        raise ValueError("union memory too large for an exhaustive comparison")
    first_positions = [index[unit.key] for unit in first.memory]
    second_positions = [index[unit.key] for unit in second.memory]
    for _, digits in _iterate_patterns(first.k, len(union)):
        a = first.local([digits[p] for p in first_positions])
        b = second.local([digits[p] for p in second_positions])
        if a != b:
            return False
    return True


def garden_of_eden(tau, cells, values, node_limit=None):
    """Decide exactly whether the pattern `values` on `cells` has no preimage.

    Returns (True, stats) for a Garden-of-Eden pattern and (False, stats) with a
    verified preimage otherwise.  With node_limit set, (None, stats) means the
    search stopped before deciding.
    """
    k = tau.k
    cells = list(cells)
    values = list(values)
    if len(cells) != len(values):
        raise ValueError("cells and values differ in length")
    seen = set()
    for cell in cells:
        if cell.key in seen:
            raise ValueError("cells must be distinct")
        seen.add(cell.key)
    for symbol in values:
        if not isinstance(symbol, int) or not 0 <= symbol < k:
            raise ValueError("pattern symbols must be integers in [0, %d)" % k)

    variables = {}
    variable_units = []
    constraints = []
    for cell, symbol in zip(cells, values):
        row = []
        for m in tau.memory:
            product = cell * m
            key = product.key
            if key not in variables:
                variables[key] = len(variable_units)
                variable_units.append(product)
            row.append(variables[key])
        constraints.append((row, symbol))

    preimages = dict((symbol, []) for symbol in range(k))
    for position, digits in _iterate_patterns(k, len(tau.memory)):
        preimages[tau.rule[position]].append(tuple(digits))
    stats = {"cells": len(cells), "variables": len(variable_units), "nodes": 0}
    for _, symbol in constraints:
        if not preimages[symbol]:
            stats["reason"] = "symbol %d is not in the image of the local rule" % symbol
            return True, stats

    remaining = list(range(len(constraints)))
    covered = set()
    ordered = []
    while remaining:
        best = max(remaining, key=lambda c: (
            sum(1 for v in constraints[c][0] if v in covered),
            -len(preimages[constraints[c][1]])))
        remaining.remove(best)
        row, symbol = constraints[best]
        ordered.append((row, preimages[symbol]))
        covered.update(row)

    assignment = [-1] * len(variable_units)
    count = len(ordered)
    choice = [0] * count
    placed_here = [None] * count
    depth = 0
    while True:
        if depth == count:
            break
        row, candidates = ordered[depth]
        if placed_here[depth]:
            for v in placed_here[depth]:
                assignment[v] = -1
            placed_here[depth] = None
        i = choice[depth]
        placed = False
        while i < len(candidates):
            pattern = candidates[i]
            i += 1
            stats["nodes"] += 1
            consistent = True
            for v, symbol in zip(row, pattern):
                current = assignment[v]
                if current != -1 and current != symbol:
                    consistent = False
                    break
            if consistent:
                fresh = [v for v in row if assignment[v] == -1]
                for v, symbol in zip(row, pattern):
                    assignment[v] = symbol
                placed_here[depth] = fresh
                placed = True
                break
        choice[depth] = i
        if node_limit is not None and stats["nodes"] > node_limit:
            return None, stats
        if placed:
            depth += 1
            if depth < count:
                choice[depth] = 0
                placed_here[depth] = None
        else:
            choice[depth] = 0
            depth -= 1
            if depth < 0:
                return True, stats

    # A preimage exists; verify it against the rule before reporting it.
    for (row, symbol) in constraints:
        digits = [assignment[v] if assignment[v] != -1 else 0 for v in row]
        if tau.local(digits) != symbol:
            raise AssertionError("garden_of_eden search produced a false preimage")
    stats["preimage_variables_assigned"] = sum(1 for a in assignment if a != -1)
    return False, stats
