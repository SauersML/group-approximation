"""Triangle presentations over PG(2,2) (Cartwright-Mantero-Steger-Zappa).

A triangle presentation compatible with a bijection lam: points -> lines is a set T
of triples (x,y,z) of points with
  (A1) for all x,y: exists z with (x,y,z) in T  iff  y lies on lam(x);
  (A2) (x,y,z) in T  =>  (y,z,x) in T;
  (A3) for all x,y: at most one z with (x,y,z) in T.
Then Gamma_T = < a_x | a_x a_y a_z = 1, (x,y,z) in T > acts simply transitively
and type-rotatingly on the vertices of an A2~ building whose Cayley complex is the
building (CMSZ I, Theorem 3.4).  Such Gamma_T have property (T).

This script enumerates T for a fixed lam by exact cover: the 21 flags (x,y) with
y in lam(x) must each be covered exactly once by a cyclic orbit of triples.
"""
import itertools, json, sys

P = list(range(7))
LINES = [frozenset({i % 7, (i + 1) % 7, (i + 3) % 7}) for i in range(7)]


def presentations(lam, limit=None):
    flags = [(x, y) for x in P for y in P if y in LINES[lam[x]]]
    orbits = []
    for x, y, z in itertools.product(P, repeat=3):
        if y in LINES[lam[x]] and z in LINES[lam[y]] and x in LINES[lam[z]]:
            orb = frozenset({(x, y), (y, z), (z, x)})
            trip = min([(x, y, z), (y, z, x), (z, x, y)])
            # an orbit covers each of its flags once; if x=y=z it is one flag
            if (x, y) == (y, z) or len(orb) == 3:
                orbits.append((trip, orb))
    orbits = list({o[0]: o for o in orbits}.values())
    by_flag = {f: [o for o in orbits if f in o[1]] for f in flags}
    out = []

    def rec(covered, chosen):
        if limit and len(out) >= limit:
            return
        free = [f for f in flags if f not in covered]
        if not free:
            T = set()
            for trip, _ in chosen:
                x, y, z = trip
                T |= {(x, y, z), (y, z, x), (z, x, y)}
            out.append(sorted(T))
            return
        f = min(free, key=lambda g: len(by_flag[g]))
        for trip, orb in by_flag[f]:
            if not (orb & covered):
                rec(covered | orb, chosen + [(trip, orb)])

    rec(frozenset(), [])
    return out


def check(T, lam):
    T = set(T)
    for x in P:
        for y in P:
            zs = [z for z in P if (x, y, z) in T]
            assert len(zs) <= 1
            assert (len(zs) == 1) == (y in LINES[lam[x]])
    for (x, y, z) in T:
        assert (y, z, x) in T
    return True


if __name__ == "__main__":
    lam = list(range(7))  # lam(i) = line {i, i+1, i+3}
    res = presentations(lam)
    print("lam = identity labelling: number of triangle presentations:", len(res))
    for T in res:
        check(T, lam)
    json.dump({"lam": lam, "T": res}, open(sys.argv[1] if len(sys.argv) > 1 else "tp_q2.json", "w"))
