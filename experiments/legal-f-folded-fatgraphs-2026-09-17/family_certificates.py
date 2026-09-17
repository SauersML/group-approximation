"""One fixed certificate for infinitely many automorphisms.

phi_1 = (a -> abb, b -> ca, c -> babb). For a positive word w(X, Y) that is empty or ends in Y, put
  phi_w = (a -> abb.w(ca, babb), b -> ca, c -> babb) = phi_1 o tau_w,  tau_w = (a -> a.w(b, c)).
The certificate of surface_phi1028.json (d^- = bc, BC) only reads phi(b), phi(c) and the gates,
which are the same for every phi_w (Df(a) = a, Df(A) = B). This script re-runs the independent
checker verify_surface.py on the SAME pairing for every such w of X/Y-length <= MAXLEN, with the
explicit inverse psi_w = tau_w^-1 o psi_1, and also checks the closed form of the characteristic
polynomial t^3 - (i+j+1) t^2 - (i+3j+5) t + 1, i = #X, j = #Y, and |chi(1)| = 2(i + 2j + 2).

usage: python3 family_certificates.py MAXLEN out.log
"""
import sys, json, itertools, subprocess, os, tempfile

MAXLEN, out = int(sys.argv[1]), sys.argv[2]
base = json.load(open("surface_phi1028.json"))
psi1 = {"a": "aaCaC", "b": "cA", "c": "bcAcAA"}


def red(w):
    o = []
    for x in w:
        if o and o[-1] == x.swapcase():
            o.pop()
        else:
            o.append(x)
    return "".join(o)


def sub(phi, w):
    return red("".join(phi[x] if x.islower() else phi[x.lower()][::-1].swapcase() for x in w))


words = [""] + ["".join(t) for L in range(1, MAXLEN + 1) for t in itertools.product("XY", repeat=L) if t[-1] == "Y"]
f = open(out, "w")
ok = 0
tmp = tempfile.mkdtemp()
for w in words:
    i, j = w.count("X"), w.count("Y")
    phi = {"a": "abb" + w.replace("X", "ca").replace("Y", "babb"), "b": "ca", "c": "babb"}
    # tau_w^-1 = (a -> a . w(b, c)^-1, b -> b, c -> c)
    tau_inv = {"a": red("a" + w.replace("X", "b").replace("Y", "c")[::-1].swapcase()), "b": "b", "c": "c"}
    psi = {x: sub(tau_inv, psi1[x]) for x in "abc"}
    cert = dict(base); cert["phi0"] = phi
    path = os.path.join(tmp, "c.json")
    json.dump(cert, open(path, "w"))
    r = subprocess.run(["python3", "verify_surface.py", path, json.dumps(psi)], capture_output=True, text=True)
    good = r.returncode == 0 and r.stdout.startswith("CERTIFICATE OK")
    rep = json.loads(r.stdout[len("CERTIFICATE OK "):]) if good else None
    closed = [1, -(i + j + 1), -(i + 3 * j + 5), 1]
    cp_ok = good and rep["charpoly"] == closed
    ok += good and cp_ok
    f.write("w=%s i=%d j=%d phi=%s psi=%s %s charpoly_closed_form=%s |chi(1)|=%d\n" % (
        w or "-", i, j, json.dumps(phi), json.dumps(psi),
        ("CERTIFICATE OK " + json.dumps(rep)) if good else "FAIL " + (r.stderr.strip().splitlines() or ["?"])[-1],
        cp_ok, 2 * (i + 2 * j + 2)))
f.write("summary: %d of %d automorphisms certified with the same pairing\n" % (ok, len(words)))
f.close()
print("summary: %d of %d" % (ok, len(words)))
