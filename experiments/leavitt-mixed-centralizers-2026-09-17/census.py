"""Census: bounded-window centralizers of small mixed-degree elements of L_{F_2}(1,2).

For each a (a sum of basis keys s_w t_v with |w|, |v| <= 2 whose degree support has
both signs) compute C_R(a) = {x in window R : ax = xa} for R = 2, 3, 4 and compare its
dimension with the number of powers 1, a, a^2, ... lying in the same window.
Print the elements whose centralizer is larger than that.

Run: python3 census.py [num_random] [seed]
"""
import sys, random, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from leavitt import window, centralizer, mul, add, ONE, degrees


def in_window(A, R):
    return all(len(w) <= R and len(v) <= R for w, v in A)


def powers_in_window(a, R, cap=40):
    n, p = 0, ONE
    while in_window(p, R) and n < cap:
        n += 1
        p = mul(p, a)
        if not p:
            break
    return n


def main():
    num = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(seed)
    W2 = window(2)
    seen = set()
    flagged = 0
    tried = 0
    while tried < num:
        k = rng.randint(2, 4)
        a = frozenset(rng.sample(W2, k))
        d = degrees(a)
        if not (d[0] < 0 < d[-1]) or a in seen:
            continue
        seen.add(a)
        tried += 1
        dims = []
        for R in (2, 3, 4):
            dims.append((len(centralizer(a, R)), powers_in_window(a, R)))
        excess = [c - p for c, p in dims]
        if any(e > 0 for e in excess):
            flagged += 1
            print(sorted(a), 'deg', d, 'dims(C_R, powers) R=2,3,4:', dims)
    print('tried', tried, 'flagged', flagged)


if __name__ == '__main__':
    main()
