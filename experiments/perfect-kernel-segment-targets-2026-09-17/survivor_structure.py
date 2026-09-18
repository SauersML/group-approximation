#!/usr/bin/env python3
"""Structure checks behind research/retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h.md (item 3).

For each of the 12 survivors of ../one-relator-hughes-free-char-p-2026-09-17/census-L12.txt (Magnus rewrites as printed by
experiments/one-relator-hughes-free-char-p-2026-09-17/segment_certify.py trace), check:

  (E)  span 2 and exponent vector e = (0, +-1, 0);
  (C0) R(1, a1, a2) is conjugate in F(a1, a2) to a1^{+-1}   (bottom cascade);
  (C2) R(a0, a1, 1) is conjugate in F(a0, a1) to a1^{+-1}   (top cascade);
  (P)  R(a0, 1, a2) lies in [F(a0,a2), F(a0,a2)]            (exponent sums 0, 0).

(E) gives the weight inequality w1 >= w0 + w2 in every lower central series; (C0) and (C2)
give <<a_j>> = <<a_{j+1}>> for interior letters of every segment.  As a calibration it also
runs the same checks on the six length-11 relators that rule 1 certified: none of them has
e = (0, +-1, 0), so the obstruction must not apply to them.

Usage: python3 survivor_structure.py
"""

SURVIVORS = [
    ("A A B a b a B A A b b", "X0x1X2x0x2"),
    ("A A B B A A b a B a b", "X0X2x0X1x2"),
    ("A A A B B a b A b a a B", "X0X1X2x0X1x2x1"),
    ("A A A B a a b b b a a B", "X0X1X2x1x0x2x1"),
    ("A A A B a a b A b a B B", "X0X1X2x1x0X1x2"),
    ("A A A b b a B A B a a b", "X2X1X0x2X1x0x1"),
    ("A A A b a a B B B a a b", "X2X1X0x1x2x0x1"),
    ("A A A b a a B A B a b b", "X2X1X0x1x2X1x0"),
    ("A A B A B A A b a B a b", "X0X2x0X1x2"),
    ("A A B a B A A b a B a b", "X1X2x1X0X1x2x0"),
    ("A A B a b a B A A b A b", "X0x1X2x0x2"),
    ("A A B a b a B A A b a b", "X2X1x0x2X1X0x1"),
]
CERTIFIED11 = ["X0X2x1X0X2", "x0x2X1x0x2", "X0x1X2X0x2", "X0X2x1X0x2", "X0x2x0X1x2",
               "X0x2X1x0x2"]


def parse(s):
    w = []
    for i in range(0, len(s), 2):
        c, d = s[i], int(s[i + 1])
        w.append((d, 1 if c == "x" else -1))
    return w


def red(w):
    out = []
    for a in w:
        if out and out[-1][0] == a[0] and out[-1][1] == -a[1]:
            out.pop()
        else:
            out.append(a)
    return out


def cred(w):
    w = red(w)
    while len(w) >= 2 and w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
        w = w[1:-1]
    return w


def kill(w, k):
    return [a for a in w if a[0] != k]


def exps(w):
    e = [0, 0, 0]
    for g, x in w:
        e[g] += x
    return e


def main():
    allok = True
    print("survivors")
    for rel, rw in SURVIVORS:
        w = parse(rw)
        e = exps(w)
        span = max(g for g, _ in w) - min(g for g, _ in w)
        c0 = cred(kill(w, 0))
        c2 = cred(kill(w, 2))
        p = exps(kill(w, 1))
        E = span == 2 and e[0] == 0 and e[2] == 0 and abs(e[1]) == 1
        C0 = len(c0) == 1 and c0[0][0] == 1
        C2 = len(c2) == 1 and c2[0][0] == 1
        P = p[0] == 0 and p[2] == 0
        allok &= E and C0 and C2 and P
        print("  %-26s %-16s e=%-12s E=%s C0=%s C2=%s P=%s" % (rel, rw, e, E, C0, C2, P))
    print("calibration: certified length-11 rewrites (obstruction must not apply)")
    for rw in CERTIFIED11:
        w = parse(rw)
        e = exps(w)
        E = e[0] == 0 and e[2] == 0 and abs(e[1]) == 1
        allok &= not E
        print("  %-16s e=%-12s E=%s" % (rw, e, E))
    print("ALL CHECKS PASS" if allok else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
