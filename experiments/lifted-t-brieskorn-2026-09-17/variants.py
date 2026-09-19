"""Test the Lochak-Schneps commutation relations (and the lifted pentagon exponent)
for the four orientation variants of (alpha, beta)."""
from pl import ID
from run import alpha, beta, order_and_shift


def w(word, a, b):
    r = ID
    for ch in word:
        r = r * {"a": a, "b": b}[ch]
    return r


X = "bab"
Y1 = "aababaa"
Y2 = "aabbaababaabbaa"
Y2alt = "aabbaabaabbaa"
for na, a in [("alpha", alpha), ("alpha^-1", alpha.inverse())]:
    for nb, b in [("beta", beta), ("beta^-1", beta.inverse())]:
        ba = b * a
        n, s = order_and_shift(ba)
        res = []
        for Y in [Y1, Y2, Y2alt]:
            x, y = w(X, a, b), w(Y, a, b)
            res.append(x * y * x.inverse() * y.inverse() == ID)
        print(na, nb, "order(ba) =", n, "lift^n = z^", s, "commutators [X,Y1],[X,Y2],[X,Y2alt] trivial:", res)
