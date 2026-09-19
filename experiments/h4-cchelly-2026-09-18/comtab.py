import sys
sys.path.insert(0, '/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
exec(open('dumpch.py').read().split("pre = sys.argv[1]")[0])
def ball(gens, L):
    lets = []
    for nm, w in gens.items():
        lets.append((nm, G.word(w))); lets.append((nm + "'", G.inv(G.word(w))))
    seen = {G.one: ''}; front = [G.one]
    for _ in range(L):
        new = []
        for g in front:
            for nm, x in lets:
                h = G.mul(g, x)
                if h not in seen:
                    seen[h] = (seen[g] + ' ' + nm).strip(); new.append(h)
        front = new
    return list(seen.items())
FB = ball(FW, int(sys.argv[1])); NB = ball(NW, int(sys.argv[2]))
def com(x, y): return G.mul(x, y) == G.mul(y, x)
for nm in sorted(NW, key=lambda s: int(s[1:])):
    x = G.word(NW[nm])
    c = [s for g, s in FB[1:] if com(x, g)]
    print(nm, 'C_F in ball:', len(c), c[:12])
for nm in sorted(FW):
    p = G.word(FW[nm])
    c = [s for g, s in NB[1:] if com(p, g)]
    print(nm, 'C_N in ball:', len(c), c[:20])
