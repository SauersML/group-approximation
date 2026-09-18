"""Closed-form power-two certificates for the family phi_k : a -> abb, b -> c a^k, c -> babb.

For k >= 1, phi_k is an automorphism with inverse
  psi_k : a -> aaCaC,  b -> cA,  c -> b (cAcAA)^k,
and chi_M(t) = t^3 - t^2 - (2k+3) t + 1. We take partial^- = {bc, CB} at power m = 2, so the four
boundary circles read (dart order of verify_surface.py)
  N1 = bc,  P1 = f^2(bc)^-1 = A^k C A^k C BBA A^k C (BBA)^k BBAB,
  N2 = CB,  P2 = f^2(CB)^-1 = babb (abb)^k c a^k abb c a^k c a^k,        |P1| = |P2| = 6k + 10,
and the pairing below is given by closed formulas in k (positions are 0-based inside a circle):

  ribbon R1   P1[k+1+i]   <-> P2[4k+4-i]     i = 0..k-1   (2nd A^k  vs 1st a^k)
  cross       P1[2k+1]    <-> P2[3k+4]                    (C vs c)
  ribbon R2   P1[2k+2+i]  <-> P2[3k+3-i]     i = 0..2     (BBA vs last abb of (abb)^k)
  ribbon R3   P1[2k+5+i]  <-> P2[5k+8-i]     i = 0..k-1   (3rd A^k  vs 2nd a^k)
  cross       P1[3k+5]    <-> P2[4k+8]                    (C vs c)
  ribbon R4   P1[3k+6+i]  <-> P2[4k+7-i]     i = 0..2     (1st BBA of (BBA)^k vs abb after a^k)
  minus       N1[0] <-> P1[3k+9],  N1[1] <-> P1[k],  N2[0] <-> P2[5k+9],  N2[1] <-> P2[3k]
  twist U     P1[i]       <-> P2[1+3i]       i = 0..k-1   (1st A^k vs the a of babb, abb^(k-1))
  twist T     P1[3k+11+3j] <-> P2[5k+10+j]   j = 0..k-1   (A's of (BBA)^(k-1) BBA vs last a^k)
              P1[3k+10]   <-> P2[3k-3]
              P1[3k+9+3j] <-> P2[3k+2-3j],  P1[3k+10+3j] <-> P2[3k-3-3j]   j = 1..k-1
              P1[6k+9]    <-> P2[2]

The script builds each certificate, runs the independent checker verify_surface.py (explicit
inverse, cubic with no rational root, M^3 > 0, (L), (2), (3), (4), connectivity, chi), and checks
chi(X) = -2(k+1), i.e. genus k + 2, with 2k + 2 vertices of valence 4 and all others of valence 2.

usage: python3 power_two_family_certificates.py KMIN KMAX out.log
"""
import sys, json, subprocess, os, tempfile

KMIN, KMAX, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
HERE = os.path.dirname(os.path.abspath(__file__))


def red(w):
    o = []
    for x in w:
        if o and o[-1] == x.swapcase():
            o.pop()
        else:
            o.append(x)
    return "".join(o)


def app(phi, w):
    return red("".join(phi[x] if x.islower() else phi[x.lower()][::-1].swapcase() for x in w))


def words(k):
    P1 = "A" * k + "C" + "A" * k + "C" + "BBA" + "A" * k + "C" + "BBA" * k + "BBAB"
    P2 = "babb" + "abb" * k + "c" + "a" * k + "abb" + "c" + "a" * k + "c" + "a" * k
    return P1, P2


def pairing(k):
    L = 6 * k + 10
    N1, P1o, N2, P2o = 0, 2, L + 2, L + 4
    P1 = lambda i: P1o + i
    P2 = lambda i: P2o + i
    pairs = []
    pairs += [(P1(k + 1 + i), P2(4 * k + 4 - i)) for i in range(k)]
    pairs += [(P1(2 * k + 1), P2(3 * k + 4))]
    pairs += [(P1(2 * k + 2 + i), P2(3 * k + 3 - i)) for i in range(3)]
    pairs += [(P1(2 * k + 5 + i), P2(5 * k + 8 - i)) for i in range(k)]
    pairs += [(P1(3 * k + 5), P2(4 * k + 8))]
    pairs += [(P1(3 * k + 6 + i), P2(4 * k + 7 - i)) for i in range(3)]
    pairs += [(N1, P1(3 * k + 9)), (N1 + 1, P1(k)), (N2, P2(5 * k + 9)), (N2 + 1, P2(3 * k))]
    pairs += [(P1(i), P2(1 + 3 * i)) for i in range(k)]
    pairs += [(P1(3 * k + 11 + 3 * j), P2(5 * k + 10 + j)) for j in range(k)]
    pairs += [(P1(3 * k + 10), P2(3 * k - 3))]
    for j in range(1, k):
        pairs += [(P1(3 * k + 9 + 3 * j), P2(3 * k + 2 - 3 * j)), (P1(3 * k + 10 + 3 * j), P2(3 * k - 3 - 3 * j))]
    pairs += [(P1(6 * k + 9), P2(2))]
    N = 2 * L + 4
    p = [None] * N
    for d, q in pairs:
        assert p[d] is None and p[q] is None, ("position used twice", k, d, q)
        p[d], p[q] = q, d
    assert None not in p, ("not a perfect matching", k)
    return p


f = open(out, "w")
tmp = tempfile.mkdtemp()
ok = 0
for k in range(KMIN, KMAX + 1):
    phi0 = {"a": "abb", "b": "c" + "a" * k, "c": "babb"}
    psi = {"a": "aaCaC", "b": "cA", "c": "b" + "cAcAA" * k}
    phi2 = {x: app(phi0, phi0[x]) for x in "abc"}
    P1, P2 = words(k)
    assert P1 == app(phi2, "bc")[::-1].swapcase() and P2 == app(phi2, "CB")[::-1].swapcase()
    labels = list("bc" + P1 + "CB" + P2)
    p = pairing(k)
    cert = {"phi0": phi0, "power": 2, "minus_words": ["bc", "CB"], "labels": labels, "pairing": p}
    fn = os.path.join(tmp, "k%d.json" % k)
    json.dump(cert, open(fn, "w"))
    r = subprocess.run([sys.executable, os.path.join(HERE, "verify_surface.py"), fn, json.dumps(psi)],
                       capture_output=True, text=True)
    line = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else r.stderr.strip().splitlines()[-1]
    good = r.returncode == 0 and line.startswith("CERTIFICATE OK")
    extra = {}
    if good:
        rep = json.loads(line[len("CERTIFICATE OK "):])
        extra["charpoly_closed_form"] = rep["charpoly"] == [1, -1, -(2 * k + 3), 1]
        extra["chi=-2(k+1)"] = rep["chi(X)"] == -2 * (k + 1)
        extra["genus=k+2"] = rep["genus of S*_f(X)"] == k + 2
        extra["valence4=2k+2"] = rep["valences"].count(4) == 2 * k + 2 and set(rep["valences"]) == {2, 4}
        good = all(extra.values())
    ok += good
    f.write("k=%d phi=%s psi=%s %s %s\n" % (k, json.dumps(phi0), json.dumps(psi), line, json.dumps(extra)))
    f.flush()
f.write("%d of %d certificates OK (k = %d..%d)\n" % (ok, KMAX - KMIN + 1, KMIN, KMAX))
f.close()
print(ok, "of", KMAX - KMIN + 1)
