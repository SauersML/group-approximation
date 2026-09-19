"""Exact multiplication data on a certified Cayley ball of Gamma_3 = <a,b,c | x^3, [[x,y],x], [[x,y],y]>.

Uses qball (finite 3-quotient Q = Gamma_3/P_K and the relator-cell certificate of w26-057):
if certify(nbr, dist, R) holds, the Q-ball of radius R is the Gamma_3-ball of radius R
(bijectively, with all Cayley edges).  Elements are indexed by their position in the Q-ball.
"""
import numpy as np
from qball import Q, ball, certify

class GroupBall:
    def __init__(self, qfile, R, extra=2):
        self.q = Q(qfile)
        self.keys, self.dist, self.nbr = ball(self.q, R + extra)
        assert certify(self.nbr, self.dist, R), "ball not certified"
        self.R = R
        N = len(self.keys)
        # inverse-generator neighbour: g * x^-1 = g * x * x
        self.nbi = np.full((3, N), -1, dtype=np.int64)
        for x in range(3):
            h = self.nbr[x]; ok = h >= 0
            h2 = np.full(N, -1, dtype=np.int64); h2[ok] = self.nbr[x][h[ok]]
            self.nbi[x] = h2
        # BFS words (generator letters 0..5: x, x^-1) for elements with dist <= R
        order = np.argsort(self.dist, kind='stable'); self.word = {0: []}
        for g in order:
            g = int(g)
            if self.dist[g] >= R: break
            for s in range(6):
                h = int(self.step(g, s))
                if h >= 0 and h not in self.word: self.word[h] = self.word[g] + [s]
        self.B = lambda r: [g for g in range(N) if self.dist[g] <= r]

    def step(self, g, s):
        return self.nbr[s][g] if s < 3 else self.nbi[s - 3][g]

    def walk(self, g, w):
        for s in w:
            g = int(self.step(g, s)); assert g >= 0
        return g

    def inv(self, g):
        w = self.word[g]
        return self.walk(0, [(s + 3) % 6 for s in reversed(w)])

    def prod(self, g, h):
        """g*h, both in the ball, with dist(g)+dist(h) <= R (so the product is inside)."""
        return self.walk(g, self.word[h])

    def auto(self, perm, signs):
        """Image of every ball element under the automorphism x_i -> x_{perm[i]}^{signs[i]}."""
        N = len(self.keys); img = np.full(N, -1, dtype=np.int64)
        for g, w in self.word.items():
            ww = []
            for s in w:
                x, e = s % 3, (1 if s < 3 else -1)
                e2 = e * signs[x]; y = perm[x]
                ww.append(y if e2 == 1 else y + 3)
            img[g] = self.walk(0, ww)
        return img
