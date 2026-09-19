"""Structure of the depth-j generator pair (a, t_j) modulo m: orbit size of I
under <a, t_j> (the image of L_j), the order of t_j, and whether t_j commutes
with a. Used to read the j-dependence of the census in census_depth*_out.txt.
"""
import sys
from gen import depth_generator, sl2_orbit


def mul(x, y, m):
    return ((x[0]*y[0] + x[1]*y[2]) % m, (x[0]*y[1] + x[1]*y[3]) % m,
            (x[2]*y[0] + x[3]*y[2]) % m, (x[2]*y[1] + x[3]*y[3]) % m)


def order(x, m):
    e, y, k = (1, 0, 0, 1), x, 1
    while y != e:
        y = mul(y, x, m); k += 1
    return k


if __name__ == '__main__':
    for m in [int(v) for v in sys.argv[1:]] or [5, 25, 9, 27]:
        full = sl2_orbit(m, 0)[0]
        for j in range(9):
            a, t = depth_generator(m, j)
            n = sl2_orbit(m, j)[0]
            comm = mul(a, t, m) == mul(t, a, m)
            print(f"m={m} j={j}: orbit={n} index={full // n} "
                  f"ord(t_j)={order(t, m)} t_j={t} commutes_with_a={comm}")
