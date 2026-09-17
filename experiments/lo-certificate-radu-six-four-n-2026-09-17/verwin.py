"""Check that the window group W(h,t) of mkwin.py maps onto Gamma_{6,4n}.
Every defining equation and every relator of W(h,t), written in the letters of Gamma_{6,4n}
(b_2, b_1, z = b_{2n}, b_4..b_h, y_i = b_{2n-i}), must be a geometric square of the datum read by
fig64n.py (convention 0). Since W's generators a1,a2,a3,b3 generate Gamma_{6,4n} (Tietze, mkelim.py),
the identity on a1,a2,a3,b3 is then an epimorphism W(h,t) -> Gamma_{6,4n}.
usage: python3 verwin.py h t n_min n_max"""
import sys
import fig64n
from bmw import parse_word


def sq(w):  # w: list of (type, signed index)
    return fig64n.canon(w)


def A(i, e=1):
    return ("a", i * e)


def B(k, e=1):
    return ("b", k * e)


def window_squares(h, t, n):
    """All squares used by W(h,t), as 4-letter words in the letters of Gamma_{6,4n}."""
    out = []
    # defining equations b2 = a3 b3 a3^-1, b1 = a3 b2 a3^-1, z = b_{2n} = a3 b1 a3^-1  (i.e. a3 b_k a3^-1 b_{k'}^-1)
    out += [[A(3), B(3), A(3, -1), B(2, -1)], [A(3), B(2), A(3, -1), B(1, -1)], [A(3), B(1), A(3, -1), B(2 * n, -1)]]
    # the Gamma_{4,4} squares and the two a2-squares
    out += [parse_word(r) for r in ("a1 b1 a2^-1 b1", "a1 b2 a2 b2^-1", "a1 b2^-1 a2^-1 b1^-1", "a1 b1^-1 a2^-1 b2")]
    out += [[A(2), B(3), A(2, -1), B(3)], [A(2), B(2 * n), A(2, -1), B(2 * n)]]
    # head: b_k = x^-1 b_{k-1} x^-1, i.e. x b_k x b_{k-1}^-1, plus x^-1 b_k a3^-1 b_{k-1}^-1 and a3 b_k x^-1 b_{k-1}^-1
    for k in range(4, h + 1):
        x = 1 if k % 2 == 0 else 2
        out += [[A(x), B(k), A(x), B(k - 1, -1)], [A(x, -1), B(k), A(3, -1), B(k - 1, -1)], [A(3), B(k), A(x, -1), B(k - 1, -1)]]
    # tail: y_i = x y_{i-1} x with y_i = b_{2n-i}; relators x^-1 y_{i-1} a3^-1 y_i^-1 and a3 y_{i-1} x^-1 y_i^-1
    for i in range(1, t + 1):
        x = 1 if i % 2 == 1 else 2
        hi, lo = 2 * n - i + 1, 2 * n - i
        out += [[A(x), B(hi), A(x), B(lo, -1)], [A(x, -1), B(hi), A(3, -1), B(lo, -1)], [A(3), B(hi), A(x, -1), B(lo, -1)]]
    return out


if __name__ == "__main__":
    h, t, n0, n1 = map(int, sys.argv[1:5])
    for n in range(n0, n1 + 1):
        datum = {fig64n.canon(fig64n.word(q, 0)) for _, _, q in fig64n.instantiate(fig64n.build(n), n)}
        ws = window_squares(h, t, n)
        missing = [w for w in ws if sq(w) not in datum]
        print("W(%d,%d) n=%d window squares=%d all in datum: %s%s" % (h, t, n, len(ws), not missing, "" if not missing else " missing " + str(missing)))
