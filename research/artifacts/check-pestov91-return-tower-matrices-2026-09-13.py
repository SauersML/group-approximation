"""Exact finite-cycle checks of the written tower maps, over F_2.

These check coordinate identities only, not the infinite-system theorem.
Run on MSI with Python 3.12; no third-party packages are needed.
"""
import json
import time


def add(*matrices):
    result = set()
    for matrix in matrices:
        result.symmetric_difference_update(matrix)
    return result


def mul(left, right):
    result = set()
    for i, j in left:
        for k, ell in right:
            if j == k:
                entry = (i, ell)
                if entry in result:
                    result.remove(entry)
                else:
                    result.add(entry)
    return result


def check_cycle(k, gaps):
    size = sum(gaps)
    starts = []
    offset = 0
    for gap in gaps:
        assert k <= gap <= 2 * k - 1
        starts.append(offset)
        offset += gap
    identity = {(i, i) for i in range(size)}
    sources = [
        {start for start, gap in zip(starts, gaps) if gap > level}
        for level in range(2 * k - 1)
    ]
    a = [{((start + level) % size, start) for start in domain}
         for level, domain in enumerate(sources)]
    b = [{(j, i) for i, j in matrix} for matrix in a]
    for i in range(len(a)):
        for j in range(len(a)):
            assert mul(b[i], a[j]) == (
                {(s, s) for s in sources[i]} if i == j else set()
            )
    assert add(*(mul(x, y) for x, y in zip(a, b))) == identity
    for row in range(size):
        for col in range(size):
            basis = {(row, col)}
            encoded = [[mul(mul(bi, basis), aj) for aj in a] for bi in b]
            decoded = add(*(
                mul(mul(a[i], encoded[i][j]), b[j])
                for i in range(len(a)) for j in range(len(a))
            ))
            assert decoded == basis
    p = {(s, s) for s in starts}
    for i in range(k):
        assert mul(b[i], a[i]) == p
    d = {(starts[0], starts[0])}
    corner_root = mul(mul(a[0], d), b[1])
    inverse_shift = {(i, (i + 1) % size) for i in range(size)}
    assert corner_root == mul(d, inverse_shift)
    assert corner_root and not mul(corner_root, corner_root)
    image = add(identity, corner_root)
    assert mul(image, image) == identity
    return {"k": k, "gaps": gaps, "cycle_size": size,
            "matrix_basis_roundtrips": size * size}


def check_greedy_markers(k, size):
    # Singleton clopen cover, with every cyclic rotation of its order.
    for rotation in range(size):
        selected = set()
        for point in list(range(size))[rotation:] + list(range(size))[:rotation]:
            forbidden = {(s + j) % size for s in selected
                         for j in range(1 - k, k)}
            if point not in forbidden:
                selected.add(point)
        ordered = sorted(selected)
        gaps = [((ordered[(i + 1) % len(ordered)] - point) % size) or size
                for i, point in enumerate(ordered)]
        assert all(k <= gap <= 2 * k - 1 for gap in gaps)
    return size


if __name__ == "__main__":
    started = time.monotonic()
    cycles = [check_cycle(2, [2, 3]), check_cycle(3, [3, 5]),
              check_cycle(4, [4, 7])]
    orders = sum(check_greedy_markers(k, size)
                 for k in range(2, 5) for size in range(k, 18))
    print(json.dumps({"field": 2, "cycles": cycles,
                      "greedy_cover_orders": orders,
                      "all_assertions_passed": True,
                      "seconds": round(time.monotonic() - started, 6)}, indent=2))
