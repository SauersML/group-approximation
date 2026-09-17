import random
from bmw import *
G = BMW(6, 5, RATTAGGI_INCOHERENT)
def ev(w):
    g = ((), ())
    for t, x in w:
        g = G.mul(g, ((x,), ()) if t == 'a' else ((), (x,)))
    return g
for r in RATTAGGI_INCOHERENT:
    assert ev(parse_word(r)) == ((), ()), r
random.seed(1)
def rnd(L):
    return ev([(random.choice('ab'), random.choice([1,2,3,4,5]) * random.choice([1,-1])) for _ in range(L)])
for _ in range(2000):
    x, y, z = rnd(6), rnd(6), rnd(6)
    assert G.mul(G.mul(x, y), z) == G.mul(x, G.mul(y, z))
    assert G.mul(x, G.inv(x)) == ((), ())
# element from the paper: a2 a1^-1 a3 a4^-1 ; check a5, a1a2^-1 commute with b1, b4
for a in [((5,), ()), ((1, -2), ())]:
    for b in [((), (1,)), ((), (4,))]:
        assert G.mul(a, b) == G.mul(b, a)
print("ok")
