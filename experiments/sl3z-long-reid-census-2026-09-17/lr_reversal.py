"""Search for a substitution sigma of F (images of x, y among words of length <= 3) with
tr rho_k(rev w) = tr rho_k(sigma(w)) for all words |w| <= 5.
If found, rev is realized as w -> J rho_k(sigma(w))^T J^-1 up to the character, which
explains why palindrome-type words a.phi(a) are rich in unipotents.
"""
import itertools
import sys

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from verify import word  # exact integer words


def tr(M): return M[0][0] + M[1][1] + M[2][2]


def img(w, sx, sy):
    inv = lambda s: s[::-1].swapcase()
    d = {'x': sx, 'y': sy, 'X': inv(sx), 'Y': inv(sy)}
    return ''.join(d[c] for c in w)


def free_reduce(w):
    out = []
    for c in w:
        if out and out[-1] == c.swapcase():
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def main(k):
    words = [''.join(p) for n in range(1, 6) for p in itertools.product('xXyY', repeat=n)]
    words = [w for w in words if free_reduce(w) == w]
    trrev = {w: tr(word(k, w[::-1])) for w in words}
    short = [free_reduce(''.join(p)) for n in (1, 2, 3) for p in itertools.product('xXyY', repeat=n)]
    short = sorted(set(s for s in short if s))
    found = []
    for sx in short:
        for sy in short:
            if all(tr(word(k, img(w, sx, sy))) == trrev[w] for w in words[:40]):
                if all(tr(word(k, img(w, sx, sy))) == trrev[w] for w in words):
                    found.append((sx, sy))
    print('k=%d: sigma with tr rho(rev w) = tr rho(sigma w), |w|<=5:' % k, found)


if __name__ == '__main__':
    for k in (4, 5, 6):
        main(k)
