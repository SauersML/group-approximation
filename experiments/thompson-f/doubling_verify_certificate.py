#!/usr/bin/env python3
"""Independent check of a doubling certificate in the positive monoid M of Thompson's group F.

Usage: doubling_verify_certificate.py CERT[.gz] MONOMIALS D NUM DEN

CERT lists one normal form per line (letters separated by commas). The script checks that the
words are distinct normal forms of degree D, computes S Y by the relations
x_j x_i = x_i x_(j+1) (i < j), and reports whether |S Y| / |Y| < NUM / DEN. It shares no code
with doubling_flow.cpp.

For example, with MONOMIALS "0,0;0,1;0,2;1,1;1,2" (the set S_(2,4) of Problem P_(2,1)),
D = 11, NUM/DEN = 2/1 on S21_11_13.txt.gz, it prints |Y| = 160430 and |S Y| = 318148.
"""
import gzip, hashlib, sys

def lml(j, w):
    out = []; k = 0
    while k < len(w) and w[k] < j:
        out.append(w[k]); j += 1; k += 1
    return tuple(out + [j] + list(w[k:]))

def mul(a, b):
    r = tuple(b)
    for j in reversed(a):
        r = lml(j, r)
    return r

def main():
    path, spec, D, num, den = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    S = [tuple(int(x) for x in m.split(",")) for m in spec.split(";")]
    raw = open(path, "rb").read()
    if path.endswith(".gz"):
        raw = gzip.decompress(raw)
    Y = [tuple(int(x) for x in line.split(",")) for line in raw.decode().splitlines() if line.strip()]
    assert len(set(Y)) == len(Y), "duplicate words"
    assert all(len(w) == D and all(w[i] <= w[i + 1] for i in range(D - 1)) for w in Y), "not normal forms of degree D"
    SY = set(mul(s, w) for s in S for w in Y)
    below = len(SY) * den < num * len(Y)
    print("|Y|", len(Y), "|SY|", len(SY), "ratio %.6f" % (len(SY) / len(Y)), "below %d/%d:" % (num, den), below,
          "sha256(uncompressed)", hashlib.sha256(raw).hexdigest())
    sys.exit(0 if below else 1)

if __name__ == "__main__":
    main()
