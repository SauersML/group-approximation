#!/usr/bin/env python3
"""acverify.py -- independent replay of acsearch certificates (counterexample swarm, 2026-09-16).

Shares no code with acsearch.c.  Letters: x, y, and X = x^-1, Y = y^-1.

State: a pair of cyclic words.  canon(w) is the least string, in Python order (X < Y < x < y),
among the rotations of w and of w^-1; the pair is sorted by (length, word).

Move (j, s, t, e), j in {0, 1}, i = 1 - j, e in {1, -1}:
    A = R_j,  B = R_i if e == 1 else R_i^-1,
    R_j <- canon(cyclic_reduce(free_reduce(A[s:] + A[:s] + B[t:] + B[:t]))),  then re-sort.
A move is a composite of the Andrews-Curtis moves (AC1)-(AC3) (artifact, Lemma 1).

Input lines (output of acsearch):
    <id> SOLVED <nstates> <k> j,s,t,e ...                 -> final state must be (X, Y)
    <id> MEET <target> <nstates> <k> moves | <m> moves     -> class after k moves == target after m moves
    <id> OPEN ...                                           -> counted, not checked
usage: acverify.py CENSUS TARGETS CERTFILE [CERTFILE ...]   (files may be .gz)
Prints one JSON object {verdict: count, ...} and the ids of verified SOLVED and MEET lines
to stdout; exit status 0 iff no checked line fails.
"""
import sys, gzip, json

INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}


def inverse(w):
    return "".join(INV[c] for c in reversed(w))


def free_reduce(w):
    st = []
    for c in w:
        if st and st[-1] == INV[c]:
            st.pop()
        else:
            st.append(c)
    return "".join(st)


def cyclic_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0] == INV[w[-1]]:
        w = w[1:-1]
    return w


def canon(w):
    return min(v[k:] + v[:k] for v in (w, inverse(w)) for k in range(len(w)))


def state(r1, r2):
    return tuple(sorted((canon(r1), canon(r2)), key=lambda r: (len(r), r)))


def exponent_det(r1, r2):
    ex = lambda r, g: r.count(g) - r.count(INV[g])
    return ex(r1, "x") * ex(r2, "y") - ex(r1, "y") * ex(r2, "x")


def signed_perm(w, p):
    """p = 4*swap + 2*[sx = -1] + [sy = -1]; x -> (swap ? y : x)^sx, y -> (swap ? x : y)^sy."""
    swap, sx, sy = p >> 2, (-1 if p & 2 else 1), (-1 if p & 1 else 1)
    img = {"x": ("y" if swap else "x", sx), "y": ("x" if swap else "y", sy)}
    out = []
    for c in w:
        g, s = img[c.lower()]
        out.append(g if s * (-1 if c.isupper() else 1) == 1 else g.upper())
    return "".join(out)


def apply(st, tok):
    f = [int(z) for z in tok.split(",")]
    if len(f) not in (4, 5):
        raise ValueError("bad token")
    j, s, t, e = f[:4]
    if j not in (0, 1) or e not in (1, -1):
        raise ValueError("bad move")
    i = 1 - j
    A, B = st[j], (st[i] if e == 1 else inverse(st[i]))
    if not (0 <= s < len(A) and 0 <= t < len(B)):
        raise ValueError("index out of range")
    new = cyclic_reduce(A[s:] + A[:s] + B[t:] + B[:t])
    if not new:
        raise ValueError("empty relator")
    if len(f) == 5:          # a signed permutation of the generators follows the move
        if not 0 <= f[4] < 8:
            raise ValueError("bad permutation")
        return state(signed_perm(new, f[4]), signed_perm(st[i], f[4]))
    return state(new, st[i])


def replay(st, toks):
    for tok in toks:
        st = apply(st, tok)
    return st


def opener(fn):
    return gzip.open(fn, "rt") if fn.endswith(".gz") else open(fn)


def main():
    census = {}
    for line in opener(sys.argv[1]):
        f = line.split()
        if len(f) == 4:
            r1, r2 = f[2], f[3]
            assert cyclic_reduce(r1) == r1 and cyclic_reduce(r2) == r2 and len(r1) + len(r2) == int(f[1])
            census[int(f[0])] = (r1, r2)
    census[-1] = ("x", "y")                       # root id -1 = the trivial presentation
    targets = [tuple(l.split()) for l in opener(sys.argv[2]) if l.strip()]
    tally, solved, meet, bad, uf = {}, [], [], [], {}

    def find(a):
        while uf.setdefault(a, a) != a:
            a = uf[a]
        return a

    for fn in sys.argv[3:]:
        for line in opener(fn):
            f = line.split()
            if len(f) < 2 or f[0] in ("END", "COMP"):
                continue
            if f[0] == "PAIR":
                # PAIR ida pa idb pb nstates k moves | m moves
                try:
                    a, pa, b, pb = int(f[1]), int(f[2]), int(f[3]), int(f[4])
                    bar = f.index("|")
                    left, right = f[6:bar], f[bar + 1:]
                    if int(left[0]) != len(left) - 1 or int(right[0]) != len(right) - 1:
                        raise ValueError("move count")
                    for c in (a, b):
                        if abs(exponent_det(*census[c])) != 1:
                            raise ValueError("det not +-1")
                    if not (0 <= pa < 8 and 0 <= pb < 8):
                        raise ValueError("bad root permutation")
                    sa = replay(state(*(signed_perm(r, pa) for r in census[a])), left[1:])
                    sb = replay(state(*(signed_perm(r, pb) for r in census[b])), right[1:])
                    if sa != sb:
                        raise ValueError("no common state")
                    verdict = "pair-equivalent-up-to-signed-permutation"
                    uf[find(a)] = find(b)
                except (ValueError, KeyError, IndexError) as exc:
                    verdict = "FAIL:" + str(exc); bad.append(f[1])
                tally[verdict] = tally.get(verdict, 0) + 1
                continue
            cid, kind = int(f[0]), f[1]
            try:
                r1, r2 = census[cid]
                if abs(exponent_det(r1, r2)) != 1:
                    raise ValueError("det not +-1")
                if kind == "SOLVED":
                    k = int(f[3])
                    toks = f[4:]
                    if len(toks) != k:
                        raise ValueError("move count")
                    if replay(state(r1, r2), toks) != ("X", "Y"):
                        raise ValueError("final state not trivial")
                    verdict = "ac-trivial"; solved.append(cid)
                elif kind == "MEET":
                    tidx, bar = int(f[2]), f.index("|")
                    left, right = f[4:bar], f[bar + 1:]
                    if int(left[0]) != len(left) - 1 or int(right[0]) != len(right) - 1:
                        raise ValueError("move count")
                    a = replay(state(r1, r2), left[1:])
                    b = replay(state(*targets[tidx]), right[1:])
                    if a != b:
                        raise ValueError("no common state")
                    verdict = "ac-equivalent-to-target-%d" % tidx; meet.append((cid, tidx))
                else:
                    verdict = "unchecked-" + kind
            except (ValueError, KeyError, IndexError) as exc:
                verdict = "FAIL:" + str(exc); bad.append(cid)
            tally[verdict] = tally.get(verdict, 0) + 1
    print(json.dumps(tally, sort_keys=True))
    print("SOLVED", " ".join(map(str, sorted(set(solved)))))
    print("MEET", " ".join("%d:%d" % p for p in sorted(set(meet))))
    comps = {}
    for a in list(uf):
        comps.setdefault(find(a), []).append(a)
    for members in sorted(sorted(m) for m in comps.values()):
        print("COMPONENT", " ".join(map(str, members)))
    if bad:
        print("FAILED", " ".join(map(str, bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
