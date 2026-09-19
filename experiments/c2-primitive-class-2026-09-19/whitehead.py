# Whitehead's algorithm on cyclic words of F_4 = <p,q,r,s>: minimise cyclic length.
# A conjugacy class is primitive iff its Whitehead-minimal cyclic length is 1.
import itertools
LET = 'pqrs'
INV = {c: c.swapcase() for c in 'pqrsPQRS'}

def inv(u): return ''.join(INV[c] for c in reversed(u))

def red(u):
    o = []
    for c in u:
        if o and o[-1] == INV[c]: o.pop()
        else: o.append(c)
    return ''.join(o)

def cyc(u):
    u = red(u)
    while len(u) > 1 and u[0] == INV[u[-1]]: u = u[1:-1]
    return u

def apply(m, u):
    return red(''.join(m[c] if c.islower() else inv(m[c.lower()]) for c in u))

def wh_autos():
    """Type-II Whitehead automorphisms (a, choice per other letter): x -> x, xa, Ax, Axa."""
    out = []
    for a in 'pqrsPQRS':
        A = INV[a]
        others = [c for c in LET if c != a.lower()]
        for ch in itertools.product(range(4), repeat=3):
            if not any(ch): continue
            m = {a.lower(): a.lower()}
            for c, k in zip(others, ch):
                m[c] = [c, c + a, A + c, A + c + a][k]
            out.append(m)
    return out
AUT = wh_autos()

def perms():
    """Type-I automorphisms are length-preserving; not needed for minimisation."""
    return []

def minimise(u):
    u = cyc(u)
    improved = True
    while improved and len(u) > 1:
        improved = False
        for m in AUT:
            v = cyc(apply(m, u))
            if len(v) < len(u):
                u, improved = v, True
                break
    return u

def is_primitive(u):
    return len(minimise(u)) == 1

if __name__ == '__main__':
    assert is_primitive('pQ') and is_primitive('pqrsPQ' + 'r') is not None
    assert not is_primitive('pqPQ') and not is_primitive('pp')
    print('self-test ok', minimise('pqrsPQ'), minimise('pqPQ'))
