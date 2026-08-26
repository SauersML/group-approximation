"""Exact union audit for the two support-return Pauli charts.

Run on MSI only.  The purpose is to test whether cross-relations between
E_1=W_1 E W_1 and E_2=W_2 E W_2 authenticate the missing third Pauli pair.
"""

from collections import deque

from support_partial_whitehead_native_return_audit import (
    A1C, A2C, A3C, B1C, B2C, B3C, E0, E000,
    conjugate_matrix, matrices_equal, matrix_key, matrix_multiply,
    pauli_closure, root, whitehead, word_matrix,
)
from depth_one_paired_leavitt_return_search import canonical


IDENTITY = identity = word_matrix(())


def faithful_matrix_key(matrix):
    def reduced(entry):
        terms = set(entry)
        changed = True
        while changed:
            changed = False
            # Completeness is the only reduction: (u0,v0)+(u1,v1)=(u,v).
            for mu, nu in sorted(terms, key=lambda pair: len(pair[1]), reverse=True):
                if not mu or not nu or not mu.endswith('0') or not nu.endswith('0'):
                    continue
                sibling = (mu[:-1] + '1', nu[:-1] + '1')
                if sibling in terms:
                    terms.remove((mu, nu))
                    terms.remove(sibling)
                    parent = (mu[:-1], nu[:-1])
                    if parent in terms:
                        terms.remove(parent)
                    else:
                        terms.add(parent)
                    changed = True
                    break
        return tuple(sorted(terms))

    return tuple(tuple(reduced(entry) for entry in row) for row in matrix)


def product(*matrices):
    answer = IDENTITY
    for matrix in matrices:
        answer = matrix_multiply(answer, matrix)
    return answer


def commutator(left, right):
    # All generators tested below are involutions.
    return product(left, right, left, right)


def closure(generators, cap=1_000_000):
    seen = {faithful_matrix_key(IDENTITY): (IDENTITY, ())}
    queue = deque(((IDENTITY, ()),))
    while queue:
        current, word = queue.popleft()
        for index, generator in enumerate(generators):
            successor = matrix_multiply(current, generator)
            key = faithful_matrix_key(successor)
            if key not in seen:
                successor_word = word + (index,)
                seen[key] = (successor, successor_word)
                queue.append((successor, successor_word))
                if len(seen) >= cap:
                    return seen, False
    return seen, True


def main():
    base_words = (
        root(4, 7, A1C), root(4, 8, A2C), root(4, 9, A3C),
        root(7, 2, B1C), root(8, 2, B2C), root(9, 2, B3C),
    )
    base = [word_matrix((word,)) for word in base_words]
    e = pauli_closure(base_words)
    assert len(e) == 128
    w1 = whitehead(7, 9, E0)
    w2 = whitehead(7, 9, E000)
    chart1 = [conjugate_matrix(w1, generator) for generator in base]
    chart2 = [conjugate_matrix(w2, generator) for generator in base]

    print('cross commutator table: 0=identity, 1=base center, 2=other')
    center = commutator(base[0], base[3])
    table = []
    other = []
    for i, left in enumerate(chart1):
        row = []
        for j, right in enumerate(chart2):
            value = commutator(left, right)
            if matrices_equal(value, IDENTITY):
                row.append(0)
            elif matrices_equal(value, center):
                row.append(1)
            else:
                row.append(2)
                other.append((i, j, value))
        table.append(row)
    for row in table:
        print(' '.join(map(str, row)))
    print('cross commutators other than identity/base center', len(other))

    generated, finite = closure(chart1 + chart2)
    print('union closure size/capped', len(generated), finite)

    # The relative support swap S=W1W2.  Test whether it belongs to the union
    # closure and whether multiplying by short union generators gives a second
    # full-chart transporter with a recognizable relation.
    s = word_matrix(w1 + w2)
    print('S in union closure', faithful_matrix_key(s) in generated)
    if finite:
        generated_keys = set(generated)
        print('base generators in union',
              [faithful_matrix_key(generator) in generated_keys for generator in base])
        print('W1 normalizes union', all(
            faithful_matrix_key(conjugate_matrix(w1, generator)) in generated_keys
            for generator in chart1 + chart2))
        print('W2 normalizes union', all(
            faithful_matrix_key(conjugate_matrix(w2, generator)) in generated_keys
            for generator in chart1 + chart2))
        print('S normalizes union', all(
            faithful_matrix_key(product(s, generator, s)) in generated_keys
            for generator in chart1 + chart2))

        # Centralizer of the exact union, restricted to the finite closure.
        centralizer = []
        for candidate, word in generated.values():
            if all(matrices_equal(matrix_multiply(candidate, generator),
                                  matrix_multiply(generator, candidate))
                   for generator in chart1 + chart2):
                centralizer.append((candidate, word))
        print('centralizer in union closure', len(centralizer))

        def conjugate_by_matrix(actor, matrix):
            return product(actor, matrix, actor)

        center_keys = {faithful_matrix_key(matrix): index
                       for index, (matrix, _) in enumerate(centralizer)}
        print('cross commutator table by exact center index')
        for left in chart1:
            print(' '.join(str(center_keys.get(
                faithful_matrix_key(commutator(left, right)), -1))
                for right in chart2))
        for index, (matrix, word) in enumerate(centralizer):
            order_two = matrices_equal(matrix_multiply(matrix, matrix), IDENTITY)
            s_image = conjugate_by_matrix(s, matrix)
            print('center', index, 'word', word, 'order2', order_two,
                  'is I/C', matrices_equal(matrix, IDENTITY), matrices_equal(matrix, center),
                  'S image', center_keys.get(faithful_matrix_key(s_image), -1))

        # Is the chart-swap automorphism inner in the exact union group?
        inner = []
        s_images = [conjugate_by_matrix(s, generator)
                    for generator in chart1 + chart2]
        for candidate, word in generated.values():
            if all(matrices_equal(conjugate_by_matrix(candidate, generator), image)
                   for generator, image in zip(chart1 + chart2, s_images)):
                inner.append(word)
        print('implementers of S automorphism inside union', len(inner), inner[:8])

        semidirect, semidirect_finite = closure(chart1 + chart2 + [s], cap=5_000)
        print('union plus S closure size/capped', len(semidirect), semidirect_finite)

        enlarged, enlarged_finite = closure(chart1 + chart2 +
                                            [word_matrix(w1), word_matrix(w2)],
                                            cap=10_000)
        print('union plus W1,W2 closure size/capped', len(enlarged), enlarged_finite)


if __name__ == '__main__':
    main()
