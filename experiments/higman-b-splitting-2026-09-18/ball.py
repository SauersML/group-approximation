"""Action of L1 = <a,b,d> on the sphere of radius r about v in the Bass-Serre tree T_B
of Gamma(3,m) = L1 *_B L2.  Vertices: words a^j1 c^k1 a^j2 ... (j1 any, others nonzero).
Writes GAP permutation lists."""
import sys, itertools
e = int(sys.argv[1]); r = int(sys.argv[2])
sys.argv = [sys.argv[0], str(e), '1']
from pathstab import push, red, inv, m

def left(s, word, j):
    """word * s^j = s^j' * word'  (word in B)."""
    w2, i2 = push(s, -j, inv(word))     # s^-j word^-1 = w2 s^i2
    return (-i2) % m, inv(w2)           # word s^j = s^-i2 w2^-1

def act(gword, vert):
    """gword: B-word or ('a',k); vert: tuple of exponents (j1,k1,j2,...)."""
    out = []; beta = gword
    for idx, x in enumerate(vert):
        s = 'a' if idx % 2 == 0 else 'c'
        x2, beta = left(s, beta, x)
        out.append(x2)
    return tuple(out)

verts = []
for js in itertools.product(range(m), *[range(1, m)] * (r - 1)):
    verts.append(js)
index = {v: i + 1 for i, v in enumerate(verts)}
def perm_of(f):
    return [index[f(v)] for v in verts]
pa = perm_of(lambda v: ((v[0] + 1) % m,) + v[1:])
pb = perm_of(lambda v: act((('b', 1),), v))
pd = perm_of(lambda v: act((('d', 1),), v))
with open('ball_e%d_r%d.g' % (e, r), 'w') as f:
    for name, p in (('pa', pa), ('pb', pb), ('pd', pd)):
        f.write('%s:=PermList(%s);;\n' % (name, p))
print(len(verts), 'vertices')
