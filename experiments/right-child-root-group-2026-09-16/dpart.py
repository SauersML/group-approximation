from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])

def phi(g):
    return mul(mul(betainv, g), beta)

def fixes_prefix0(g):
    # g acts as identity on [0]
    for w, F in g.items():
        if w.startswith('0') and F != frozenset([w]):
            return False
        if w == '':
            return F == frozenset([''])
    # leaves above '0'? if '' is a leaf handled; otherwise leaves start with 0 or 1
    return True

def dpart(g):
    """(1,1) corner: strip prefix 1: d(g) delta_y = [1]-part of g delta_{1y}, with prefix 1 removed."""
    g = dict(g)
    if '' in g:
        split_leaf(g, '')
    out = {}
    for w, F in g.items():
        if w.startswith('1'):
            out[w[1:]] = frozenset(v[1:] for v in F if v.startswith('1'))
    return canon(out)

for name, g in [('u', u), ('x', x), ('y', y)]:
    h = g
    for k in range(0, 4):
        assert fixes_prefix0(h), (name, k)
        print(name, k, 'd =', sorted((w, sorted(F)) for w, F in dpart(h).items()))
        h = phi(h)
