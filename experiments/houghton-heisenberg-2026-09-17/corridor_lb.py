"""Y-corridor lower bound for areas of words in Houghton's group H_3.

Presentation (Lee, arXiv:1212.0257, Thm C, n = 3): generators X = g_1 = lambda_(1,2),
Y = g_2 = lambda_(1,3), a = alpha = ((1,1),(1,2)); relators
  a^2, (a a^X)^3, [a, a^(X^2)], [X,Y] a^-1, a^(X^-1) (a^(Y^-1))^-1.
Every relator has Y-exponent 0 and at most two Y-letters, so in any van Kampen
diagram the boundary Y-edges are paired by Y-corridors whose sides are words in
X, a.  If the corridor joins boundary Y-edges i < j, the boundary arc strictly
between them equals a side word U in H_3, so the arc element lies in
H_2 = <X, a> (it fixes ray 3 pointwise).  Every cell adds at most one letter
a^(+-1) to each side, and inv (inversions w.r.t. the order of the line
ray2-reversed + ray1) is subadditive with inv(X^(+-1)) = 0, inv(a) = 1 (X is
order preserving on the line, a swaps two adjacent line points).  Hence

   corridor length >= inv(arc element),
   Area(w) >= min over non-crossing admissible matchings of sum inv(arc).

(The column area_lb3 = sum_inv_min / 3 is the cruder per-letter bound, kept for
comparison with earlier runs.)  For the family 'ga' the hand proof in
research/houghton-h3-at-least-cubic-dehn-corridor-proof.md shows the matching
is forced, with sum m^2 (m - 1); the DP reproduces this for m <= 8.

Conventions: right actions, words applied left to right (first letter first),
points (r, p) with rays r in {1,2,3} and depth p >= 0.  Letters: 'X','x','Y',
'y','a' with lower case = inverse.
"""
import sys
import numpy as np


def build(B):
    """Arrays for the letters on points r*B + p (r = 0,1,2 for rays 1,2,3).
    Pushing past depth B-1 goes to the sink index 3B."""
    S = 3 * B
    def idx(r, p):
        return r * B + p if p < B else S

    def lam(x, y):
        f = np.arange(S + 1)
        for p in range(B):
            f[idx(x, p)] = idx(x, p - 1) if p >= 1 else idx(y, 0)
            f[idx(y, p)] = idx(y, p + 1)
        return f

    def inv(f):
        g = np.full(S + 1, S)
        for i in range(S):
            if f[i] != S:
                g[f[i]] = i
        return g
    X = lam(0, 1)
    Y = lam(0, 2)
    a = np.arange(S + 1)
    a[idx(0, 0)], a[idx(0, 1)] = idx(0, 1), idx(0, 0)
    return {'X': X, 'x': inv(X), 'Y': Y, 'y': inv(Y), 'a': a}, S


def prefixes(word, L, S):
    """P[k] = element of word[:k] as an array: point -> image."""
    P = [np.arange(S + 1)]
    for c in word:
        P.append(L[c][P[-1]])      # apply previous prefix, then letter c
    return P


def inverse_arr(f, S):
    g = np.full(S + 1, S)
    ok = f[:S] != S
    g[f[:S][ok]] = np.arange(S)[ok]
    g[S] = S
    return g


def lower_bound(word, verbose=False, same_sign_ok=False):
    N = len(word)
    B = 6 * N + 20
    L, S = build(B)
    P = prefixes(word, L, S)
    Pinv = [inverse_arr(f, S) for f in P]
    W = 3 * N + 5
    # line points in line order: ray 2 depths W-1..0, then ray 1 depths 0..W-1
    line = np.array([1 * B + p for p in range(W - 1, -1, -1)] + [0 * B + p for p in range(W)])
    pos = np.full(S + 1, -10 ** 9)
    fullline = np.array([1 * B + p for p in range(B - 1, -1, -1)] + [0 * B + p for p in range(B)])
    pos[fullline] = np.arange(len(fullline))
    ray3 = np.array([2 * B + p for p in range(W)])
    Yidx = [k for k, c in enumerate(word) if c in 'Yy']
    K = len(Yidx)
    INF = float('inf')
    cost = {}
    for s in range(K):
        for t in range(s + 1, K, 2):
            i, j = Yidx[s], Yidx[t]
            if word[i] == word[j] and not same_sign_ok:
                continue
            # arc element = word[i+1:j] = P[i+1]^-1 then P[j]
            beta = P[j][Pinv[i + 1]]
            if not np.array_equal(beta[ray3], ray3):
                continue
            img = pos[beta[line]]
            if img.min() < 0:
                raise RuntimeError('window too small')
            n = len(img)
            invs = int(np.sum(np.triu(img[:, None] > img[None, :], 1)))
            cost[(s, t)] = invs
    # interval DP for min-cost non-crossing perfect matching
    f = {}
    for length in range(0, K + 1, 2):
        for s in range(0, K - length + 1):
            e = s + length - 1
            if length == 0:
                f[(s, e)] = 0
                continue
            best = INF
            for t in range(s + 1, e + 1, 2):
                c = cost.get((s, t))
                if c is None:
                    continue
                inner = f[(s + 1, t - 1)] if t - 1 >= s + 1 else 0
                outer = f[(t + 1, e)] if e >= t + 1 else 0
                v = c + inner + outer
                if v < best:
                    best = v
            f[(s, e)] = best
    return f[(0, K - 1)] if K else 0, cost


def pw(s, k):
    return s * k


def inv_word(w):
    sw = {'X': 'x', 'x': 'X', 'Y': 'y', 'y': 'Y', 'a': 'a'}
    return ''.join(sw[c] for c in reversed(w))


def comm(u, v):  # u^-1 v^-1 u v
    return inv_word(u) + inv_word(v) + u + v


if __name__ == '__main__':
    fam = sys.argv[1] if len(sys.argv) > 1 else 'wm'
    ms = [int(x) for x in sys.argv[2:]] or [1, 2, 3, 4, 5, 6]
    for m in ms:
        if fam == 'wm':
            s = pw('X', m) + pw('Y', m) + pw('x', m) + pw('y', m)
            z = pw('xY', m)
            w = s + z + inv_word(s) + inv_word(z)
        elif fam == 'sz':      # [s_m, Z]
            s = pw('X', m) + pw('Y', m) + pw('x', m) + pw('y', m)
            w = s + 'xY' + inv_word(s) + 'yX'
        elif fam == 'sq':      # [X^m, Y^m] times its inverse written differently: trivial check
            s = pw('X', m) + pw('Y', m) + pw('x', m) + pw('y', m)
            w = s + inv_word(s)
        elif fam == 'ga':      # [Y^m X^m Y^-m, alpha]
            g = pw('Y', m) + pw('X', m) + pw('y', m)
            w = comm(g, 'a')
        elif fam == 'xt':      # [X^m, alpha^(Y^m)], alpha^(Y^m) on ray 3
            w = comm(pw('X', m), pw('y', m) + 'a' + pw('Y', m))
        elif fam == 'gz':      # [Y^m X^m Y^-m, alpha^(X^-m)]... far transposition on ray 1
            g = pw('Y', m) + pw('X', m) + pw('y', m)
            w = comm(g, pw('X', m) + 'a' + pw('x', m))
        else:
            raise SystemExit('unknown family')
        import os
        lb, cost = lower_bound(w, same_sign_ok=bool(os.environ.get('SAME_SIGN_OK')))
        extra = ''
        if fam == 'ga':
            extra = ' hand_formula_m2(m-1) %d' % (m * m * (m - 1))
        print(fam, m, 'len', len(w), 'sum_inv_min', lb, 'area_lb', lb,
              'area_lb3', round(lb / 3.0, 3), extra, flush=True)
