"""Machine check of the case analysis (i)-(iv) in
research/houghton-h3-at-least-cubic-dehn-corridor-proof.md.

For w_m = [g, a] = g^-1 a^-1 g a with g = Y^m X^m Y^-m, i.e.
    Y^m X^-m Y^-m a Y^m X^m Y^-m a       (a = alpha, a^-1 = a),
label the Y-letters A = a_1..a_m, B = b_1..b_m, C = c_1..c_m, D = d_1..d_m.
A pair of opposite-sign Y-letters is admissible when the arc strictly between
them fixes ray 3 pointwise (necessary for lying in H_2 = <X, a>).  We check:
  * a_i is admissible only with b_(m+1-i), at cost (inversions) k*m, k = m-i;
  * no a_i is admissible with any d_j;
  * c_i is admissible with d_j only for j = m+1-i, at cost k*m, k = m-i;
  * the forced total is m^2 (m-1).
Also checks the two HNN relators Y X Y^-1 = a X and Y a Y^-1 = X a X^-1.
"""
import sys
from corridor_lb import lower_bound, comm, pw, inv_word
from sanity import is_trivial

assert is_trivial('YXy' + inv_word('aX'))
assert is_trivial('Yay' + inv_word('Xax'))
print('HNN relators rho_X, rho_a trivial: ok')

ms = [int(x) for x in sys.argv[1:]] or [2, 3, 4, 5, 6, 7, 8]
for m in ms:
    g = pw('Y', m) + pw('X', m) + pw('y', m)
    w = comm(g, 'a')
    assert w == pw('Y', m) + pw('x', m) + pw('y', m) + 'a' + g + 'a'
    assert is_trivial(w)
    lb, cost = lower_bound(w)
    # Y-letter indices 0..4m-1: A = 0..m-1, B = m..2m-1, C = 2m..3m-1, D = 3m..4m-1
    name = {}
    for i in range(m):
        name[i] = ('a', i + 1)
        name[m + i] = ('b', i + 1)
        name[2 * m + i] = ('c', i + 1)
        name[3 * m + i] = ('d', i + 1)
    adm = {}
    for (s, t), c in cost.items():
        adm.setdefault(s, {})[t] = c
        adm.setdefault(t, {})[s] = c
    total = 0
    for i in range(1, m + 1):
        k = m - i
        pa = {name[t]: c for t, c in adm.get(i - 1, {}).items()}
        assert pa == {('b', m + 1 - i): k * m}, (m, i, pa)
        pc = {name[t]: c for t, c in adm.get(2 * m + i - 1, {}).items() if name[t][0] == 'd'}
        assert pc == {('d', m + 1 - i): k * m}, (m, i, pc)
        total += 2 * k * m
    assert total == m * m * (m - 1) == lb, (m, total, lb)
    print('m', m, 'len', len(w), 'forced matching ok, sum inv', total, '= m^2(m-1); DP min', lb)
