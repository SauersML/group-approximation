import sys, json, random, time, math
from primes import *
lo, hi, secs, seed, seedfile = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
seeds = []
for line in open(seedfile):
    if line.startswith("PRIME"):
        d = json.loads(line[6:])
        if d["pieces"] >= 9:
            seeds.append(frozenset(tri(*[tuple(v) for v in t]) for t in d["tris"]))
rnd = random.Random(seed); t0 = time.time(); found = {}; steps = 0
while time.time() - t0 < secs:
    F = rnd.choice(seeds)
    target = rnd.randint(lo, hi)
    while len(F) < target:
        ed = edges_of(F)
        F = fan_edge_blowup(F, rnd.choice(list(ed)), ed) if rnd.random() < 0.6 else face_blowup(F, rnd.choice(list(F)))
    s = len(mergeable(F)); temp = 2.0
    for _ in range(3000):
        if time.time() - t0 > secs: break
        ed = edges_of(F); n = len(F); r = rnd.random(); G = None
        if r < 0.55:
            fl = flops(F, ed)
            if fl: G = do_flop(F, rnd.choice(fl))
        elif r < 0.8:
            bd = fan_blowdowns(F)
            if bd and n > lo: G = do_fan_blowdown(F, rnd.choice(bd))
        elif r < 0.92:
            if n < hi: G = fan_edge_blowup(F, rnd.choice(list(ed)), ed)
        else:
            if n < hi: G = face_blowup(F, rnd.choice(list(F)))
        if G is None: continue
        steps += 1; s2 = len(mergeable(G))
        if s2 <= s or rnd.random() < math.exp(-(s2 - s) / temp):
            F, s = G, s2
            if s == 0 and len(F) >= lo:
                k = canon(F)
                if k not in found: check(F); found[k] = F
        temp = max(0.1, temp * 0.999)
sizes = {}
for F in found.values(): sizes[len(F)] = sizes.get(len(F), 0) + 1
print(json.dumps({"mode": "seeded", "lo": lo, "hi": hi, "seed": seed, "steps": steps, "nseeds": len(seeds), "prime_fans_by_size": dict(sorted(sizes.items()))}))
for F in sorted(found.values(), key=len)[-3:]:
    print("PRIME", json.dumps(describe(F)))
