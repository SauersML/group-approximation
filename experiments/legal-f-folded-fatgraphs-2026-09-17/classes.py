"""Group the automorphisms of phi_scan4.json into classes under letter permutation and word
reversal (conjugation by the automorphism x -> x^-1 composed with inversion of images), both of
which give isomorphic mapping tori and transport legal f-folded fatgraphs.

usage: python3 classes.py census.log [verdict-prefix]
prints one line per class: representative index, class size, verdict set of its members
"""
import sys, json, itertools

log = sys.argv[1]
want = sys.argv[2] if len(sys.argv) > 2 else None
verdict = {}
phis = {}
for line in open(log):
    if line.startswith("stats") or line.startswith("chunk"):
        continue
    n = int(line.split()[0])
    phis[n] = json.loads(line[line.index("{"):line.index("}") + 1])
    verdict[n] = line.rsplit("polys=", 1)[1].split(None, 1)[1].split()[0]


def canon(phi):
    best = None
    for perm in itertools.permutations("abc"):
        s = dict(zip("abc", perm))
        for rev in (False, True):
            q = {s[x]: "".join(s[y] for y in phi[x]) for x in "abc"}
            if rev:
                q = {x: q[x][::-1] for x in q}
            key = json.dumps(q, sort_keys=True)
            best = key if best is None or key < best else best
    return best


cls = {}
for n in sorted(phis):
    cls.setdefault(canon(phis[n]), []).append(n)
for key, members in sorted(cls.items(), key=lambda kv: kv[1][0]):
    vs = sorted({verdict[n] for n in members})
    if want is None or any(v.startswith(want) for v in vs):
        print(members[0], len(members), ",".join(vs), key)
