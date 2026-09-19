# The width-3 presentation r' = eDDEdd CB eDDEdd bDcd (c' = cB): levels, F_4 words, and the free-factor facts
# used in the node: A = <e_-2, e_-1, c'_2> is not a free factor, and {<e_-2,e_-1>, <c'_2>} is not a free factor system.
from nsearch import *
from ff import is_free_factor, core
IMG = {'b': 'b', 'c': 'cB', 'd': 'd', 'e': 'e'}
R3 = 'eDDEddCBeDDEddbDcd'
OLD = cyc(app(IMG, R3)); assert tofib(toxy(OLD)) == '' and canon(OLD) == canon(cyc(R)), OLD
print('width', width(R3, IMG))
w = {}
for g, j in [('e', -2), ('e', -1), ('e', 0), ('c', 2), ('c', 3), ('b', 0)]:
    t = 'd'; eg = eps(IMG[g]); g0 = toxy(IMG[g]) + (('Y' * eg) if eg > 0 else ('y' * (-eg)))
    x = ('y' * j + g0 + 'Y' * j) if j >= 0 else ('Y' * (-j) + g0 + 'y' * (-j))
    w[(g, j)] = tofib(red(x)); print(g, j, w[(g, j)])
f = red(w[('e', 0)] + inv(w[('e', -2)]))
c3 = red(inv(w[('b', 0)]) + f + w[('b', 0)] + w[('c', 2)] + f)
print('c_3 = b0^-1 f b0 c2 f :', c3 == w[('c', 3)])
A = [w[('e', -2)], w[('e', -1)], w[('c', 2)]]
print('A free factor:', is_free_factor(A))
print('<e-2,e-1> free factor:', is_free_factor(A[:2]), ' <e-2,e-1,e0>:', is_free_factor([w[('e', j)] for j in (-2, -1, 0)]))
print('c2 core (cyclic word):', core([w[('c', 2)]])[1].__len__(), ' {<pQ,qR>,<s>} jointly:', is_free_factor(['pQ', 'qR', 's']))
print("c'_2 primitive:", is_free_factor([w[('c', 2)]]), "  {<e-2,e-1>} u {<c'_2>} :", is_free_factor(A))
from ff import is_ffs
print("{<e-2,e-1>, <c'_2>} FFS up to conjugacy:", is_ffs([A[:2], [A[2]]]), "  {<e-2,e-1,e0>, <c'_2>}:", is_ffs([[w[('e', j)] for j in (-2, -1, 0)], [A[2]]]))
print("sanity: {<p,q>,<qrQ>}:", is_ffs([['p', 'q'], ['qrQ']]), " {<p>,<p q p Q>}:", is_ffs([['p'], ['pqpQ']]))
