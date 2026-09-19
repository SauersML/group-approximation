"""A malnormal rank-3 target with deep < law at Q = one point.

B = <x, y, z>, x = aBAB, y = bbAA, z = AbaBa   (rank 3, malnormal: malnormal.py)
A = <x, y^2, z^3> <= B.
law = rk(B rel A) = 2: B / <<A>> = Z/2 * Z/3 needs 2 generators (Grushko),
  and <A, y, z> = B.
deep = 1: the single seed (base, vertex read by a^-1 b a^-1) of core(A)
  has fold closure containing ker(core(A) -> core(B)) (exact fold closure).
Also prints the rank/malnormality status of every target used in this folder.
"""
from chains import analyse, pair_graphs
from malnormal import malnormal, rank
from foldlib import closure, contains_kernel

A = ['aBAB', 'bbAAbbAA', 'AbaBaAbaBaAbaBa']
B = ['aBAB', 'bbAA', 'AbaBa']

print('B rank', rank(B), 'malnormal', malnormal(B)[0])
dk, lk, wit = analyse([0], [0], A, B, 4)[:3]
print('Q = point: deep', dk, 'law', lk)
GB, GA, m = pair_graphs([0], [0], A, B)
u, v = wit[0]
wd = ''.join(l if e == 1 else l.upper() for l, e in GA.word[v][1])
print('witness seed: base and vertex read by', wd,
      'closure contains ker:', contains_kernel(GA, closure(GA, [(u, v)]), m))

TARGETS = {
    'L_1 = <a, baBB>': ['a', 'baBB'],
    'L_2 = <a, phi(t_1)>': ['a', 'baBBabbAbAB'],
    '<a, t^2>': ['a', 'baBBbaBB'],
    '<ab, ba>': ['ab', 'ba'],
    '<a, baaB>': ['a', 'baaB'],
    '<a, baBaB>': ['a', 'baBaB'],
    '<a^2, b, aba^-1>': ['aa', 'b', 'abA'],
    'B above': B,
}
for k, ws in TARGETS.items():
    print('%-22s rank %d malnormal %s' % (k, rank(ws), malnormal(ws)[0]))
