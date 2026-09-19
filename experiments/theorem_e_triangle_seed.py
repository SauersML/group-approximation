"""Exact exploratory checks for the proposed Theorem E seed; NOT a Lean proof.

Source: Caprace--Conder--Kaluba--Witzel, arXiv:2011.09276,
Section 7.2 and Proposition 7.15, G_HB_2^(2)(7), scalar blocks equal to 1.
Run from the repository root with Python 3. No external packages are needed.
This checks a finite matrix image, not infinitude, hyperbolicity, property (T),
or torsion-freeness of the kernel of the presented-group homomorphism.
"""

from collections import deque
import json

P = 7
N = 4
IDENTITY = tuple(int(i == j) for i in range(N) for j in range(N))


def mul(a, b):
    return tuple(
        sum(a[N * i + k] * b[N * k + j] for k in range(N)) % P
        for i in range(N) for j in range(N)
    )


def inverse(a):
    rows = [list(a[N * i:N * (i + 1)])
            + [int(i == j) for j in range(N)] for i in range(N)]
    for col in range(N):
        pivot = next(i for i in range(col, N) if rows[i][col] % P)
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = pow(rows[col][col], -1, P)
        rows[col] = [(x * scale) % P for x in rows[col]]
        for i in range(N):
            if i != col:
                scale = rows[i][col]
                rows[i] = [(x - scale * y) % P
                           for x, y in zip(rows[i], rows[col])]
    result = tuple(x for row in rows for x in row[N:])
    if mul(a, result) != IDENTITY or mul(result, a) != IDENTITY:
        raise ValueError("matrix inverse check failed")
    return result


def power(a, n):
    result = IDENTITY
    while n:
        if n % 2:
            result = mul(result, a)
        a = mul(a, a)
        n //= 2
    return result


def commutator(*args):
    """Left-associated commutator, [x,y] = x^-1 y^-1 x y."""
    result = args[0]
    for b in args[1:]:
        result = mul(mul(mul(inverse(result), inverse(b)), result), b)
    return result


def elementary_sum(*entries):
    result = list(IDENTITY)
    for i, j, value in entries:  # One-based matrix indices from the paper.
        result[N * (i - 1) + j - 1] = (
            result[N * (i - 1) + j - 1] + value) % P
    return tuple(result)


def pair_order(a, b, limit):
    generators = (a, b, inverse(a), inverse(b))
    seen = {IDENTITY}
    pending = deque([IDENTITY])
    while pending:
        x = pending.popleft()
        for g in generators:
            y = mul(x, g)
            if y not in seen:
                seen.add(y)
                if len(seen) > limit:
                    raise ValueError("pair subgroup exceeds its expected order")
                pending.append(y)
    return len(seen)


def main():
    a = elementary_sum((1, 4, 1), (2, 3, 1))
    b = elementary_sum((2, 1, 1), (3, 4, -1))
    c = elementary_sum((4, 2, 1))
    relators = [power(a, P), power(b, P), power(c, P),
                commutator(a, b, a), commutator(a, b, b),
                commutator(c, b, c), commutator(c, b, b, c),
                commutator(c, b, b, b), commutator(c, a, c),
                commutator(c, a, a, c), commutator(c, a, a, a)]
    if len(relators) != 11 or any(r != IDENTITY for r in relators):
        raise ValueError("a defining relator failed")
    orders = {"ab": pair_order(a, b, P**3),
              "bc": pair_order(b, c, P**4),
              "ca": pair_order(c, a, P**4)}
    if orders != {"ab": 343, "bc": 2401, "ca": 2401}:
        raise ValueError(f"unexpected pair orders: {orders}")
    print(json.dumps({"field": P, "relators_checked": len(relators),
                      "pair_image_orders": orders,
                      "lean_certificate": False}, indent=2))


if __name__ == "__main__":
    main()
