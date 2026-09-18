# Turn the class-level cycles found by kpure2.py --powers into explicit certificates for verify_klein2.py.
# Consecutive cycle entries in different families are an inverting step (K); entries in the same family are a
# power step, certified by the common root r (the key computed by powkey in kpure2.py) as an (R) step.
# usage: collect.py census.json out.json kpp.jsonl [kpp.jsonl ...]
import sys, json
D = json.load(open(sys.argv[1])); iA, iB = D['iA'], D['iB']
def winv(w, inv): return tuple(inv[c] for c in reversed(w))
def root(f, w):                      # same normalisation as powkey in kpure2.py
    inv = iA if f == 'h' else iB
    w = list(w); u = []
    while len(w) >= 2 and w[0] == inv[w[-1]]:
        u.append(w[0]); w = w[1:-1]
    c = tuple(w); N = len(c); u = tuple(u)
    p = next(c[:d] for d in range(1, N + 1) if N % d == 0 and c == c[:d] * (N // d))
    j = 1 if len(p) % 2 == 0 else 2
    r = u + p * j + winv(u, inv)
    return min(r, winv(r, inv))
def parse(s):
    a, b = s.split('|'); a, b = a[1:], b[1:]
    return ('v', tuple(map(int, a))) if a else ('h', tuple(map(int, b)))
def fmt(f, w): return ('v' + ''.join(map(str, w)) + '|h') if f == 'v' else ('v|h' + ''.join(map(str, w)))
out = {}
for fn in sys.argv[3:]:
    for line in open(fn):
        rec = json.loads(line)
        if not rec['cycle']: continue
        cyc = rec['cycle']; roots = {}
        for i in range(len(cyc)):
            (f1, w1), (f2, w2) = parse(cyc[i]), parse(cyc[(i + 1) % len(cyc)])
            if f1 == f2:
                r = root(f1, w1); assert r == root(f2, w2)
                roots[str(i)] = fmt(f1, r)
        out[str(rec['class'])] = {'chain': cyc, 'roots': roots} if roots else cyc
json.dump(out, open(sys.argv[2], 'w'), indent=0); print(len(out), 'chains written to', sys.argv[2])
