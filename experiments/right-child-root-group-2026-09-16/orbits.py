"""Orbit sizes of basis vectors delta_z under finitely generated subgroups of the germ kernel K_0 of
Gamma' = <u,x,y,beta>.  Points are long explicit strings; the depth into the tail that the orbit
reaches is tracked, to detect escape (possible infinite orbit)."""
import sys, random
from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])

def phi(g):
    return mul(mul(betainv, g), beta)

def conj_beta(g, k):
    # beta^k g beta^-k for k possibly negative
    h = g
    if k >= 0:
        for _ in range(k):
            h = mul(mul(beta, h), betainv)
    else:
        for _ in range(-k):
            h = mul(mul(betainv, h), beta)
    return h

def orbit(gens, z, cap=200000, taillen_min=40):
    start = frozenset([z])
    seen = {start}
    stack = [start]
    minlen = len(z)
    while stack:
        v = stack.pop()
        for g in gens:
            out = {}
            for p in v:
                res = apply_to_word(g, p)
                if res is None:
                    raise ValueError('point too short')
                for q in res:
                    out[q] = out.get(q, 0) ^ 1
            w = frozenset(q for q, c in out.items() if c)
            for q in w:
                minlen = min(minlen, len(q))
            if w not in seen:
                seen.add(w)
                stack.append(w)
                if len(seen) > cap:
                    return None, minlen
        if minlen < taillen_min:
            return None, minlen
    return len(seen), minlen

if __name__ == '__main__':
    K = int(sys.argv[1])
    mode = sys.argv[2]
    random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    gens = []
    for g in [u, x, y]:
        for k in range(-K, K + 1):
            gens.append(conj_beta(g, k))
    print('generators', len(gens), 'max depth', max(depth(g) for g in gens))
    L = 400
    for trial in range(8):
        if mode == 'random':
            z = ''.join(random.choice('01') for _ in range(L))
        elif mode == 'ones':
            pre = ''.join(random.choice('01') for _ in range(6))
            z = pre + '1' * (L - 6)
        elif mode == 'zeros':
            pre = ''.join(random.choice('01') for _ in range(6))
            z = pre + '0' * (L - 6)
        elif mode == 'period':
            pre = ''.join(random.choice('01') for _ in range(6))
            per = random.choice(['01', '011', '0111', '001', '10110'])
            z = pre + (per * L)[:L - 6]
        n, ml = orbit(gens, z)
        print(mode, 'trial', trial, 'orbit size', n, 'min length reached', ml, 'of', L, flush=True)
