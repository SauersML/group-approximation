"""Exact check of the generalized-torsion identity in G(K; -1, 1) = <y, t | y_1^K = [y_0^-1, y_2]>:
  P1 = y_0 y_2 y_0^-1,  P2 = y_3^-1 y_1 y_3,
  P1 . (y_2^K P2)^(K-1) . y_2^(K-1) . (y_2 P2 y_2^-1) = 1,
a product of K^2 + K conjugates of y.  Decided by Britton's lemma (tower_wp).  As a control, the same word is
checked in G(K; 1, 1) and G(K; 1, -1), where it must be nontrivial (else the bi-order search would be moot).
"""
from tower_wp import Tower, inv


def word(K):
    y = lambda i: ((i, 1),)
    P1 = y(0) + y(2) + inv(y(0))
    P2 = inv(y(3)) + y(1) + y(3)
    w = P1 + (y(2) * K + P2) * (K - 1) + y(2) * (K - 1) + y(2) + P2 + inv(y(2))
    return w, 1 + (K - 1) * (K + 1) + (K - 1) + 1


for K in range(1, 6):
    w, m = word(K)
    res = {ab: Tower(K, *ab).trivial_N(w) for ab in [(-1, 1), (1, 1), (1, -1)]}
    print('K', K, 'conjugates', m, 'trivial in (-1,1):', res[(-1, 1)], ' (1,1):', res[(1, 1)], ' (1,-1):', res[(1, -1)])
    assert res[(-1, 1)]
