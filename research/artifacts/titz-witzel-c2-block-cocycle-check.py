#!/usr/bin/env python3
"""Dependency-free checks for the C2-block Titz--Witzel cocycle formulae."""

from __future__ import annotations

import random


Word = tuple[int, ...]
Pair = tuple[tuple[Word, Word], int]


def reduce_word(word: Word) -> Word:
    out: list[int] = []
    for letter in word:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def word_mul(left: Word, right: Word) -> Word:
    return reduce_word(left + right)


def word_inv(word: Word) -> Word:
    return tuple(-letter for letter in reversed(word))


def swap(pair: tuple[Word, Word]) -> tuple[Word, Word]:
    return pair[1], pair[0]


IDENTITY: Pair = (((), ()), 0)


def pair_mul(left: Pair, right: Pair) -> Pair:
    a, epsilon = left
    b, delta = right
    if epsilon:
        b = swap(b)
    return (
        (word_mul(a[0], b[0]), word_mul(a[1], b[1])),
        epsilon ^ delta,
    )


def pair_inv(value: Pair) -> Pair:
    components, epsilon = value
    answer = (word_inv(components[0]), word_inv(components[1]))
    if epsilon:
        answer = swap(answer)
    return answer, epsilon


def pair_pow(value: Pair, exponent: int) -> Pair:
    if exponent < 0:
        return pair_pow(pair_inv(value), -exponent)
    answer = IDENTITY
    for _ in range(exponent):
        answer = pair_mul(answer, value)
    return answer


def conjugate(left: Pair, middle: Pair) -> Pair:
    return pair_mul(pair_mul(left, middle), pair_inv(left))


def derive(e: Pair, u: Pair) -> dict[str, Pair]:
    h = conjugate(u, e)
    a = conjugate(e, h)
    x = pair_mul(a, pair_pow(u, 2))
    c = pair_mul(pair_mul(pair_pow(u, 2), a), pair_pow(u, 2))
    f = conjugate(pair_inv(x), h)
    d = pair_mul(pair_mul(e, pair_inv(a)), f)
    s = pair_mul(pair_mul(f, a), f)
    rho = pair_mul(pair_mul(pair_inv(x), pair_inv(s)), pair_inv(c))
    beta = conjugate(rho, e)
    p = pair_mul(beta, a)
    return {
        "h": h,
        "a": a,
        "x": x,
        "c": c,
        "f": f,
        "d": d,
        "s": s,
        "rho": rho,
        "beta": beta,
        "p": p,
    }


def symbolic_checks() -> None:
    p_word, q_word = (1,), (2,)
    e: Pair = (((), ()), 1)
    u: Pair = ((p_word, q_word), 1)
    got = derive(e, u)

    P, Q = p_word, q_word
    H0, H1 = word_mul(P, word_inv(Q)), word_mul(Q, word_inv(P))
    A0, A1 = H1, H0
    V0, V1 = word_mul(P, Q), word_mul(Q, P)
    X0, X1 = word_mul(A0, V1), word_mul(A1, V0)
    C0 = word_mul(word_mul(V0, A0), V1)
    C1 = word_mul(word_mul(V1, A1), V0)
    F0 = word_mul(word_mul(word_inv(X1), H1), X0)
    F1 = word_mul(word_mul(word_inv(X0), H0), X1)
    D0, D1 = word_mul(word_inv(A0), F0), word_mul(word_inv(A1), F1)
    S0 = word_mul(word_mul(F0, A1), F0)
    S1 = word_mul(word_mul(F1, A0), F1)
    R0 = word_mul(word_mul(word_inv(X1), word_inv(S0)), word_inv(C1))
    R1 = word_mul(word_mul(word_inv(X0), word_inv(S1)), word_inv(C0))
    B0, B1 = word_mul(R0, word_inv(R1)), word_mul(R1, word_inv(R0))
    T0, T1 = word_mul(B0, A1), word_mul(B1, A0)

    expected = {
        "h": ((H0, H1), 1),
        "a": ((A0, A1), 1),
        "x": ((X0, X1), 1),
        "c": ((C0, C1), 1),
        "f": ((F0, F1), 1),
        "d": ((D0, D1), 1),
        "s": ((S0, S1), 1),
        "rho": ((R0, R1), 1),
        "beta": ((B0, B1), 1),
        "p": ((T0, T1), 0),
    }
    assert got == expected

    c, rho, beta, a, d, p = (
        got["c"], got["rho"], got["beta"], got["a"], got["d"], got["p"]
    )
    relators = {
        "c2": pair_pow(c, 2),
        "root": pair_mul(pair_mul(pair_pow(rho, 2), e), pair_inv(u)),
        "chain": pair_mul(pair_mul(pair_mul(beta, a), u), pair_inv(d)),
        "sandwich": pair_mul(pair_mul(pair_mul(p, u), p), c),
        "mark": pair_pow(u, 8),
    }
    asserted = {
        "c2": ((word_mul(C0, C1), word_mul(C1, C0)), 0),
        "root": (
            (word_mul(word_mul(R0, R1), word_inv(P)),
             word_mul(word_mul(R1, R0), word_inv(Q))),
            0,
        ),
        "chain": (
            (word_mul(word_mul(T0, P), word_inv(D0)),
             word_mul(word_mul(T1, Q), word_inv(D1))),
            0,
        ),
        "sandwich": (
            (word_mul(word_mul(word_mul(T0, P), T1), C1),
             word_mul(word_mul(word_mul(T1, Q), T0), C0)),
            0,
        ),
        "mark": (((P + Q) * 4, (Q + P) * 4), 0),
    }
    assert relators == asserted


Perm = tuple[int, ...]


def perm_identity(size: int) -> Perm:
    return tuple(range(size))


def perm_mul(left: Perm, right: Perm) -> Perm:
    return tuple(left[right[index]] for index in range(len(left)))


def perm_inv(value: Perm) -> Perm:
    answer = [0] * len(value)
    for source, target in enumerate(value):
        answer[target] = source
    return tuple(answer)


def perm_pow(value: Perm, exponent: int) -> Perm:
    if exponent < 0:
        return perm_pow(perm_inv(value), -exponent)
    answer = perm_identity(len(value))
    for _ in range(exponent):
        answer = perm_mul(answer, value)
    return answer


def hamming(left: Perm, right: Perm) -> float:
    return sum(a != b for a, b in zip(left, right)) / len(left)


def concrete_pair_mul(
    left: tuple[tuple[Perm, Perm], int], right: tuple[tuple[Perm, Perm], int]
) -> tuple[tuple[Perm, Perm], int]:
    a, epsilon = left
    b, delta = right
    if epsilon:
        b = b[1], b[0]
    return ((perm_mul(a[0], b[0]), perm_mul(a[1], b[1])), epsilon ^ delta)


def concrete_pair_pow(value: tuple[tuple[Perm, Perm], int], exponent: int):
    size = len(value[0][0])
    answer = ((perm_identity(size), perm_identity(size)), 0)
    for _ in range(exponent):
        answer = concrete_pair_mul(answer, value)
    return answer


def pair_action(value: tuple[tuple[Perm, Perm], int]) -> Perm:
    (a0, a1), epsilon = value
    size = len(a0)
    out = []
    for block in range(2):
        for point in range(size):
            target_block = block ^ epsilon
            component = (a0, a1)[target_block]
            out.append(target_block * size + component[point])
    return tuple(out)


def randomized_metric_checks() -> None:
    rng = random.Random(0xC2B10C)
    for size in range(2, 11):
        identity = perm_identity(size)
        for _ in range(100):
            p_list, q_list = list(range(size)), list(range(size))
            rng.shuffle(p_list)
            rng.shuffle(q_list)
            P, Q = tuple(p_list), tuple(q_list)
            e = ((identity, identity), 1)
            u = ((P, Q), 1)

            # The pair multiplication rule agrees with actual permutations.
            assert pair_action(concrete_pair_mul(u, e)) == perm_mul(
                pair_action(u), pair_action(e)
            )

            mark = pair_action(concrete_pair_pow(u, 8))
            pq, qp = perm_mul(P, Q), perm_mul(Q, P)
            mu = hamming(mark, perm_identity(2 * size))
            assert abs(mu - hamming(perm_pow(pq, 4), identity)) < 1e-12

            ue, eu = concrete_pair_mul(u, e), concrete_pair_mul(e, u)
            assert abs(
                hamming(pair_action(ue), pair_action(eu)) - hamming(P, Q)
            ) < 1e-12

            u2 = concrete_pair_pow(u, 2)
            u2e, eu2 = concrete_pair_mul(u2, e), concrete_pair_mul(e, u2)
            assert abs(
                hamming(pair_action(u2e), pair_action(eu2)) - hamming(pq, qp)
            ) < 1e-12


def main() -> None:
    symbolic_checks()
    randomized_metric_checks()
    print("C2-block cocycle formulae: PASS")
    print("randomized block-metric identities: PASS")


if __name__ == "__main__":
    main()
