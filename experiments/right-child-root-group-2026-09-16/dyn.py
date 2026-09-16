from leavitt_ops import *
import random
u = ident_plus([('0', '1')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])
u2 = mul(mul(beta, y), betainv)
G = mul(u, u2); Gi = mul(u2, u)
random.seed(1)
tail = ''.join(random.choice('01') for _ in range(60))
def act(g, vec):
    return act_vec(g, vec)
for start in ['0', '1', '00', '01', '10', '11']:
    z = start + tail
    for name, g in [('G', G), ('Gi', Gi)]:
        v = {z: 1}
        out = []
        for n in range(1, 7):
            v = act(g, v)
            pre = sorted(set(w[:4] for w in v))
            out.append((n, len(v), pre))
        print(start, name, out[-1][1], [o[2] for o in out[-2:]])
