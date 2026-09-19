"""Excise a k x l block of the n x n torus into its own k x l torus; the cone component has one 6pi point."""
from swap import tori, excess, profile
from stalls_lib import components, restrict
from handle import best_handle
import sys
def excise_block(n, k, l):
    b, c = tori([(n, n)]); P = lambda i, j: (j % n)*n + (i % n)
    for j in range(l):
        b[P(-1, j)] = P(k, j); b[P(k-1, j)] = P(0, j)
    for i in range(k):
        c[P(i, -1)] = P(i, l); c[P(i, l-1)] = P(i, 0)
    return b, c
if __name__ == '__main__':
    for (n, k, l) in [(10, 2, 2), (10, 3, 3), (12, 4, 4), (12, 2, 5), (14, 5, 5)]:
        b, c = excise_block(n, k, l)
        cm = max(components(b, c), key=len); B, C = restrict(b, c, cm)
        pr = profile(b, c, 2*max(k, l) + 2)
        print(n, k, l, 'excess', excess(B, C), 'profile>=', round(pr[0], 3), pr[1], 'handle', best_handle(B, C, max(k, l)), flush=True)
