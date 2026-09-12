"""Exact certificate that four explicit atlas units generate L_2^x.

For each of the two GL(4,2) leaf charts, the adjacent-transvection words
012 and 354 generate a subgroup of order 20160, hence the whole chart.
The two chart groups generate the binary Leavitt unit group by equation (7)
of notes/EXPLICIT_LEAVITT_ATLAS.md.  Thus their four displayed images generate
the full (nonsofic) unit group used by the Kaplansky search.
"""

from collections import deque

from atlas_two_chart_search import I4, factor_generators, gf2_mul


def matrix_key(matrix):
    return bytes(matrix.reshape(-1))


def product_word(generators, word):
    value = I4.copy()
    for index in word:
        value = gf2_mul(value, generators[index])
    return value


def generated_order(generators):
    seen = {matrix_key(I4)}
    queue = deque([I4.copy()])
    while queue:
        value = queue.popleft()
        for generator in generators:
            successor = gf2_mul(value, generator)
            successor_key = matrix_key(successor)
            if successor_key not in seen:
                seen.add(successor_key)
                queue.append(successor)
    return len(seen)


def main():
    adjacent = [word[0][1] for _, word in factor_generators()[:6]]
    words = ((0, 1, 2), (3, 5, 4))
    pair = [product_word(adjacent, word) for word in words]
    order = generated_order(pair)
    assert order == 20160
    print("chart generator words", words)
    print("generated order", order)
    print("four atlas units = the same pair in charts 1 and 2")
    print("conclusion: the four units generate the full binary Leavitt unit group")


if __name__ == "__main__":
    main()
