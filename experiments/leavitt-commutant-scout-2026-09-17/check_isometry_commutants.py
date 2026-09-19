"""Exact check of leavitt-isometry-centralizers-are-monogenic on finite boxes:
the commutant of s_w (and t_w) inside V_{N,L} should be spanned by the powers of
s_u (resp. t_u) lying in the box, u the primitive root of w."""
from l2 import El, ONE
from commutant import commutant
s, t = El.s, El.t

def show(name, A, N, L):
    C = commutant(A, N, L)
    print(name, 'box V_%d,%d' % (N, L), 'dim', len(C))
    for c in C:
        print('   ', c.reduce())

for w in ['0', '01', '0101']:
    show('C(s_%s)' % w, s(w), 2, 4)
    show('C(t_%s)' % w, t(w), 2, 4)
