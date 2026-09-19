"""Check det and the image of C = <a,b> in SL_3(Z/m) for small m.

Pair from research/explicit-sl3-thin-codense-tau-pair.md.
"""
import sys

a = [[-176379047, 1936571625, -17817867],
     [-1941616205, 21318171799, -196142682],
     [10, -121, 1]]
b = [[-40193888, -3684209, -44180039],
     [396162230, 36312596, 435450841],
     [3829559, 351021, 4209349]]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def factor(m):
    f, p = {}, 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def sl3_order(m):
    o = 1
    for p, e in factor(m).items():
        o *= p ** (8 * (e - 1)) * p ** 3 * (p ** 2 - 1) * (p ** 3 - 1)
    return o


def image_size(m):
    A = tuple(x % m for r in a for x in r)
    B = tuple(x % m for r in b for x in r)

    def mul(X, Y):
        return tuple(sum(X[3 * i + k] * Y[3 * k + j] for k in range(3)) % m
                     for i in range(3) for j in range(3))
    I = (1, 0, 0, 0, 1, 0, 0, 0, 1)
    seen = {I}
    fr = [I]
    while fr:
        nf = []
        for X in fr:
            for g in (A, B):
                Y = mul(X, g)
                if Y not in seen:
                    seen.add(Y)
                    nf.append(Y)
        fr = nf
    return len(seen)


if __name__ == "__main__":
    print("det a =", det3(a), " det b =", det3(b))
    mods = [int(x) for x in sys.argv[1:]] or [2, 3, 4, 5, 8, 9]
    for m in mods:
        s, o = image_size(m), sl3_order(m)
        print(f"m={m}: |image|={s}  |SL3(Z/m)|={o}  surjective={s == o}")
