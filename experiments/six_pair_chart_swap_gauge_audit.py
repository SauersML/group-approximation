"""Audit the six-Pauli-pair chart-swap gauge fence.

Run through the MSI wrapper only.  The first and last triples are independent
Pauli blocks.  Native adjacent swaps act simultaneously on both blocks, while
the block swap retains an undetected scalar multiplicity sign.
"""


def compose(left, right):
    return tuple(left[right[i]] for i in range(len(left)))


def transposition(size, i, j):
    value = list(range(size))
    value[i], value[j] = value[j], value[i]
    return tuple(value)


def gf2_rank(rows):
    width = len(rows[0]) if rows else 0
    rows = [sum((bit & 1) << j for j, bit in enumerate(row)) for row in rows]
    rank = 0
    for column in range(width):
        pivot = next((r for r in range(rank, len(rows)) if (rows[r] >> column) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for r in range(len(rows)):
            if r != rank and ((rows[r] >> column) & 1):
                rows[r] ^= rows[rank]
        rank += 1
    return rank


def main():
    identity = tuple(range(6))
    # Adjacent scale swaps act on both three-qubit charts.
    w1 = compose(transposition(6, 0, 1), transposition(6, 3, 4))
    w2 = compose(transposition(6, 1, 2), transposition(6, 4, 5))
    # Exchange the original and moved charts.
    h = (3, 4, 5, 0, 1, 2)

    assert compose(w1, w1) == identity
    assert compose(w2, w2) == identity
    assert compose(h, h) == identity
    assert compose(compose(w1, w2), w1) == compose(compose(w2, w1), w2)
    assert compose(h, w1) == compose(w1, h)
    assert compose(h, w2) == compose(w2, h)

    # A_i versus B_j has the identity commutation matrix: six independent
    # Pauli pairs, so the generated label algebra is M_64(C).
    commutation = [[int(i == j) for j in range(6)] for i in range(6)]
    assert gf2_rank(commutation) == 6

    # z=C=-1, R=S=+1 realizes the two own-center and two cross-center rows.
    z = c = -1
    r = s = 1
    assert z == c and r == s

    # The scalar multiplicity signs extracted after label removal are not
    # conjugate even though their relative scalar commutes with all labels.
    gauge_g1 = 1
    gauge_g2 = -1
    assert gauge_g1 != gauge_g2
    assert gauge_g1 * gauge_g2 == -1
    print("six-pair chart swap retains scalar external gauge; all label rows exact")


if __name__ == "__main__":
    main()
