"""The phi_1 certificate in every fibre rank n >= 4, with a Pisot characteristic polynomial.

For k >= 1 let d_1, ..., d_k be new letters, n = k + 3, and
  phi_k : a -> a^7 c^9 d_1 b,  b -> ca,  c -> babb,  d_i -> d_{i+1} (i < k),  d_k -> b.
Part A (exact, all k at once): with A(t) = t^3 - 7t^2 - 13t - 7,
  * A has one real root in (8, 9) and two complex roots of modulus < 1 (exact discriminant);
  * G(x) = |A(e^{i s})|^2 - |1 + e^{i s}|^2, written as a polynomial in x = cos s, has no root in
    [-1, 1] and is positive there (sympy exact real-root count).
So by Rouche chi_k(t) = t^k A(t) - (t + 1) has exactly one root outside the closed unit disk and
none on the circle, hence it is irreducible for every k.
Part B (k = 1..KMAX): build phi_k and the closed-form inverse
  psi(b) = d_k,  psi(a) = D_k c D_k D_k,  psi(c) = b psi(a)^-1,  psi(d_{i+1}) = d_i,
  psi(d_1) = psi(a^6 c^9)^-1 psi(a)^-1 a psi(b)^-1,
run verify_surface_rankn.py (inverse, positivity, |det| = 1, primitivity, exact irreducibility,
non-palindromic chi_{M^2} for even n, fatgraph checks on the unchanged pairing of
surface_phi1028.json), and compare chi_M with t^k A(t) - (t + 1).

usage: python3 pisot_chain_family.py KMAX out.log
"""
import sys, json, subprocess, os, tempfile
import sympy

KMAX, out = int(sys.argv[1]), sys.argv[2]
f = open(out, "w")

# ---------- Part A: exact, uniform in k ----------
t, x, s = sympy.symbols("t x s")
A = t**3 - 7*t**2 - 13*t - 7
assert A.subs(t, 8) < 0 < A.subs(t, 9)
disc = sympy.discriminant(A, t)
assert disc < 0  # one real root theta, a complex pair with |z|^2 = 7 / theta < 7/8
assert sympy.Poly(A, t).count_roots() == 1
# |P(e^{is})|^2 = sum_{j,l} p_j p_l cos((j - l) s), then cos(m s) = T_m(x)
def sq_mod_on_circle(coeffs):  # coeffs low -> high
    tot = 0
    for j, pj in enumerate(coeffs):
        for l, pl in enumerate(coeffs):
            tot += pj * pl * sympy.chebyshevt(abs(j - l), x)
    return sympy.expand(tot)
Acoef = [-7, -13, -7, 1]
Bcoef = [1, 1]
G = sympy.Poly(sq_mod_on_circle(Acoef) - sq_mod_on_circle(Bcoef), x)
nroots = G.count_roots(-1, 1)
Gmin = min(float(G.eval(sympy.Rational(i, 1000))) for i in range(-1000, 1001))
assert nroots == 0 and G.eval(0) > 0
# spot check the trig identity numerically
import cmath, math
for sv in (0.3, 1.7, 2.9, math.pi):
    z = cmath.exp(1j * sv)
    lhs = abs(z**3 - 7*z**2 - 13*z - 7)**2 - abs(z + 1)**2
    assert abs(lhs - float(G.eval(sympy.nsimplify(math.cos(sv))))) < 1e-6 * max(1, abs(lhs))
f.write("partA A=t^3-7t^2-13t-7 disc=%s real_roots=1 root_in_(8,9)=True G(x)=%s roots_in_[-1,1]=%d min_on_grid=%.6f RouchE_OK\n"
        % (disc, G.as_expr(), nroots, Gmin))

# ---------- Part B: per-k certificates ----------
CHAIN = "defghijklmnopqrstuvwxyz" + "αβγδεζηθικλμνξοπρ"
assert KMAX <= len(CHAIN)
base = json.load(open("surface_phi1028.json"))
def red(w):
    o = []
    for y in w:
        if o and o[-1] == y.swapcase():
            o.pop()
        else:
            o.append(y)
    return "".join(o)
inv = lambda w: w[::-1].swapcase()
app = lambda m, w: "".join(m[y] if y.islower() else inv(m[y.lower()]) for y in w)
X = "a" * 6 + "c" * 9
ok = 0
tmp = tempfile.mkdtemp()
for k in range(1, KMAX + 1):
    d = CHAIN[:k]
    phi = {"a": "a" + X + d[0] + "b", "b": "ca", "c": "babb"}
    for i in range(k - 1):
        phi[d[i]] = d[i + 1]
    phi[d[-1]] = "b"
    psi = {"b": d[-1], "a": red(inv(d[-1]) + "c" + inv(d[-1]) + inv(d[-1]))}
    psi["c"] = red("b" + inv(psi["a"]))
    for i in range(k - 1):
        psi[d[i + 1]] = d[i]
    psi[d[0]] = red(inv(app(psi, X)) + inv(psi["a"]) + "a" + inv(psi["b"]))
    cert = {"phi0": phi, "power": 1, "minus_words": base["minus_words"], "pairing": base["pairing"]}
    path = os.path.join(tmp, "c.json")
    json.dump(cert, open(path, "w"))
    r = subprocess.run(["python3", "verify_surface_rankn.py", path, json.dumps(psi)], capture_output=True, text=True)
    good = r.returncode == 0 and r.stdout.startswith("CERTIFICATE OK")
    rep = json.loads(r.stdout[len("CERTIFICATE OK "):]) if good else None
    closed = [1, -7, -13, -7] + [0] * (k - 2) + [-1, -1] if k >= 2 else [1, -7, -13, -8, -1]
    cp_ok = good and rep["charpoly"] == closed
    ok += good and cp_ok
    f.write("k=%d n=%d phi=%s psi=%s %s charpoly_closed_form=%s\n" % (
        k, k + 3, json.dumps(phi, ensure_ascii=False), json.dumps(psi, ensure_ascii=False),
        ("CERTIFICATE OK " + json.dumps(rep)) if good else "FAIL " + (r.stderr.strip().splitlines() or ["?"])[-1],
        cp_ok))
    f.flush()
f.write("summary: %d of %d ranks certified with the same pairing\n" % (ok, KMAX))
f.close()
print("summary: %d of %d" % (ok, KMAX))
