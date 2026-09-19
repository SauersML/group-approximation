# Hill-climb over relator-slide deletions Gamma''(kappa) of (C2), minimising the number of
# homomorphisms to small simple groups with t != 1.  kappa_z (z != z0) is a product of conjugates
# pre_i t^{m_i} pre_i^-1; the linearisation (the certificate) is fixed by the moves below:
#   M1 multiply a prefix on the right by v W v^-1, W in {w, w^-1, t, t^-1} (W maps to 1 in G);
#   M2 append a commutator [v1 t v1^-1, v2 t^{+-1} v2^-1] to kappa_z;
#   M3 swap two adjacent factors of kappa_z.
# Gamma''(kappa) = <t,x,y | u_0(SUB), u_1(SUB)>, SUB z = kappa_z^-1 phi(z), SUB z0 = t phi(z0);
# Gamma''/<<t>> = G for every state, and N = <<t>> is perfect.  N = 1 would prove RP(H,G).
import sys, os, random, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_unimodular import D, BAS, U0, U1, inv, fred, W
from slide import cyc
import homs
def init_state(D, z0):
    eps, u = D[z0][0]; ui = inv(u)
    st = {'z0': z0, 'k': {}}
    for z in 'abcde':
        if z == z0: continue
        st['k'][z] = [[wd + ui, -eps * n] for n, wd in D[z]]
    return st
def factor_word(f):
    pre, m = f[0], f[1]
    if m == 0: return pre   # m == 0 marks a raw word factor (commutators)
    return pre + ('t' if m > 0 else 'T') * abs(m) + inv(pre)
def relators(st):
    SUB = {}
    for z, fs in st['k'].items():
        SUB[z] = fred(inv(''.join(factor_word(f) for f in fs)) + BAS[z])
    SUB[st['z0']] = 't' + BAS[st['z0']]
    def subst(v): return fred(''.join(SUB[ch] if ch.islower() else inv(SUB[ch.lower()]) for ch in v))
    return cyc(subst(U0)), cyc(subst(U1))
def rword(n): return fred(''.join(random.choice('xyXY') for _ in range(n)))
def mutate(st):
    st = json.loads(json.dumps(st))
    z = random.choice(sorted(st['k']))
    fs = st['k'][z]
    r = random.random()
    if r < 0.6:
        f = random.choice([f for f in fs if f[1] != 0])
        v = rword(random.randint(0, 3))
        Wd = random.choice([W, inv(W), 't', 'T'])
        f[0] = fred(f[0] + v + Wd + inv(v))
    elif r < 0.85:
        a = rword(random.randint(0, 2)); b = rword(random.randint(0, 2))
        A = a + 't' + inv(a); B = b + random.choice('tT') + inv(b)
        fs.insert(random.randint(0, len(fs)), [fred(A + B + inv(A) + inv(B)), 0])
    else:
        if len(fs) > 1:
            i = random.randrange(len(fs) - 1); fs[i], fs[i + 1] = fs[i + 1], fs[i]
    return st
def score(st, groups=('A5', 'PSL27')):
    R0, R1 = relators(st)
    return [homs.count(R0, R1, g)[0] for g in groups], len(R0) + len(R1)
if __name__ == '__main__':
    seed = int(sys.argv[1]); secs = float(sys.argv[2]); z0 = sys.argv[3] if len(sys.argv) > 3 else 'c'
    random.seed(seed)
    cur = init_state(D, z0); sc, L = score(cur); best = (sum(sc), L)
    print('start', sc, L, flush=True)
    t0 = time.time(); it = 0
    while time.time() - t0 < secs:
        it += 1
        new = mutate(cur)
        if len(''.join(relators(new))) > 2500: continue
        s, L = score(new)
        if (sum(s), L) <= best or random.random() < 0.05:
            cur = new; best = (sum(s), L) if (sum(s), L) <= best else best
            print(it, s, L, flush=True)
            if sum(s) == 0:
                s2, _ = score(cur, ('S5', 'A6', 'PGL27', 'PSL211'))
                print('  ZERO; further', s2, flush=True)
                json.dump(cur, open('zero_%d_%d.json' % (seed, it), 'w'))
                if sum(s2) == 0: break
    json.dump(cur, open('last_%d.json' % seed, 'w'))
