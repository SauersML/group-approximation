"""Greedy iteration of the donor two-swap chain (chain2) on random clustered perturbations of tori.
Each step: for every excess-positive component, pad with a donor in DONORS, take the shortest chain of
<= 2 swaps (first excess-neutral, second lowering; L1<=3, L2<=5). Report stalls and total cost."""
import random, json, subprocess, sys, os
from swap import tori, inv, excess
from stalls_lib import components, restrict
from tchain import pad
DONORS = [None, (1, 1), (2, 1), (1, 2), (2, 2)]
def chain(b, c, L1=3, L2=5):
    best = None
    for dn in DONORS:
        B, C = (b, c) if dn is None else pad(b, c, *dn)
        inp = f"{len(B)}\n" + " ".join(map(str, B)) + "\n" + " ".join(map(str, C)) + "\n"
        r = subprocess.run(['./chain2', str(L1), str(L2)], input=inp, capture_output=True, text=True,
                           timeout=1200, env=dict(os.environ, PAIR='1'))
        lines = r.stdout.split('\n')
        if 'total' not in lines[1]: continue
        tot = int(lines[1].split('total ')[1].split(' ')[0])
        v = list(map(int, lines[2].split()[1:])); n = len(B)
        if best is None or tot < best[0]: best = (tot, dn, v[:n], v[n:])
    return best
def run(seed, trials):
    rng = random.Random(seed); stalls = []; stats = []
    for trial in range(trials):
        sizes = [(rng.randrange(4, 10), rng.randrange(4, 10)) for _ in range(rng.randrange(1, 3))]
        b0, c0 = tori(sizes); d = len(b0); m = rng.randrange(2, 6)
        s0 = rng.randrange(d); pts = {s0}; r = rng.randrange(1, 4); fr = [s0]
        for _ in range(r):
            fr = [g[y] for y in fr for g in (b0, c0, inv(b0), inv(c0))]; pts |= set(fr)
        if rng.random() < 0.3: pts |= {rng.randrange(d) for _ in range(3)}
        pts = sorted(pts); b, c = b0[:], c0[:]
        for g, g0 in ((b, b0), (c, c0)):
            sup = rng.sample(pts, min(m, len(pts))); perm = sup[:]; rng.shuffle(perm)
            for u, v in zip(sup, perm): g[u] = g0[v]
        ex = excess(b, c)
        if ex == 0: continue
        comps = [restrict(b, c, cm) for cm in components(b, c)]
        steps = []; stuck = None
        while True:
            bad = [i for i, (B, C) in enumerate(comps) if excess(B, C) > 0]
            if not bad: break
            i = bad[0]; B, C = comps[i]; res = chain(B, C)
            if res is None: stuck = (B, C); break
            steps.append((res[0], res[1])); comps.pop(i)
            comps += [restrict(res[2], res[3], cm) for cm in components(res[2], res[3])]
        stats.append(dict(trial=trial, ex=ex, m=m, steps=steps, stuck=stuck is not None))
        print(trial, 'excess', ex, 'm', m, 'steps', steps, 'STUCK' if stuck else 'ok', flush=True)
        if stuck: stalls.append(dict(trial=trial, b=stuck[0], c=stuck[1]))
    return stats, stalls
if __name__ == '__main__':
    seed, trials = int(sys.argv[1]), int(sys.argv[2])
    st, sl = run(seed, trials)
    json.dump(dict(stats=st, stalls=sl), open(f'greedy2_seed{seed}.json', 'w'))
    print('trials', len(st), 'stuck', sum(s['stuck'] for s in st),
          'max steps', max(len(s['steps']) for s in st), 'max chain', max((x[0] for s in st for x in s['steps']), default=0))
