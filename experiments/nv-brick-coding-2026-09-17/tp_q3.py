"""Search triangle presentations over PG(2,3) (13 points, lines {i,i+1,i+3,i+9} mod 13)
for random point-line bijections lam, by exact cover of the 52 flags."""
import random, json, sys
n = 13
LINES = [frozenset({i % n, (i + 1) % n, (i + 3) % n, (i + 9) % n}) for i in range(n)]


def presentations(lam, limit=1):
    flags = [(x, y) for x in range(n) for y in range(n) if y in LINES[lam[x]]]
    orbits = {}
    for x, y in flags:
        for z in LINES[lam[y]]:
            if x in LINES[lam[z]]:
                orb = frozenset({(x, y), (y, z), (z, x)})
                if len(orb) == 3 or x == y == z:
                    orbits[min([(x, y, z), (y, z, x), (z, x, y)])] = orb
    by_flag = {f: [] for f in flags}
    for t, o in orbits.items():
        for f in o:
            by_flag[f].append((t, o))
    out = []

    def rec(covered, chosen):
        if len(out) >= limit:
            return
        free = [f for f in flags if f not in covered]
        if not free:
            T = set()
            for (x, y, z) in chosen:
                T |= {(x, y, z), (y, z, x), (z, x, y)}
            out.append(sorted(T))
            return
        f = min(free, key=lambda g: sum(1 for t, o in by_flag[g] if not (o & covered)))
        for t, o in by_flag[f]:
            if not (o & covered):
                rec(covered | o, chosen + [t])

    rec(frozenset(), [])
    return out


if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    found = []
    for trial in range(20000):
        lam = list(range(n))
        random.shuffle(lam)
        r = presentations(lam)
        if r:
            found.append((lam, r[0]))
            print("found at trial", trial, flush=True)
            if len(found) >= 2:
                break
    json.dump({"examples": found}, open("tp_q3.json", "w"))
    print("done", len(found))
