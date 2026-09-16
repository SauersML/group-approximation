from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])
for name, g in [('u', u), ('x', x), ('y', y)]:
    print(name, g, 'sq=id', is_ident(mul(g, g)))
print('beta', beta)
print('beta*betainv', is_ident(mul(beta, betainv)), is_ident(mul(betainv, beta)))
u2 = mul(mul(beta, y), betainv)
print('beta y beta^-1 =', u2)
G = mul(u, u2)
P = IDENT
for n in range(1, 8):
    P = mul(P, G)
    print(n, 'depth', depth(P), 'size', size(P), 'id?', is_ident(P))
