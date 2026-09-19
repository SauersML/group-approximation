#!/usr/bin/env python3
"""Deep Nielsen-image search for the 26 open words: breadth-first over images under
elementary Nielsen moves of F(a, b) (depth <= DEPTH, length <= |w| + SLACK), each image
certified by the landed rules + rule R + rule N (nilpotent_root_certify.py).

Usage: nielsen_deep.py DEPTH SLACK WORD ...
"""
import os
import sys

S = os.environ.get("W10", "")
sys.path.insert(0, os.path.join(S, "experiments", "amalgam-segment-steps-2026-09-17"))
sys.path.insert(0, os.path.join(S, "experiments", "perfect-kernel-segment-targets-2026-09-17"))
import nilpotent_root_certify as asc  # noqa: E402

hc = asc.hc
asc.rsc.MODE["R"] = True
asc.MODE["A"] = True


def parse(s):
    return tuple((0 if c in "aA" else 1, 1 if c.islower() else -1) for c in s)


def show(w):
    return "".join(("ab"[a] if e == 1 else "AB"[a]) for a, e in w)


def main():
    depth, slack = int(sys.argv[1]), int(sys.argv[2])
    for s in sys.argv[3:]:
        w0 = hc.canon(hc.cred(parse(s)))
        seen, frontier = {w0}, [w0]
        hit = None
        minlen = len(w0)
        for d in range(1, depth + 1):
            nxt = []
            for u in frontier:
                for mv in asc.NIELSEN_MOVES:
                    v = hc.canon(hc.cred(hc.subst(u, mv)))
                    if v in seen or len(v) > len(w0) + slack:
                        continue
                    seen.add(v)
                    nxt.append(v)
                    minlen = min(minlen, len(v))
                    ok, why = hc.certify(v, "new", memo={})
                    if ok:
                        hit = (d, show(v), why)
                        break
                if hit:
                    break
            if hit:
                break
            frontier = nxt
        print(s, "images=%d minlen=%d" % (len(seen), minlen), hit if hit else "none", flush=True)


if __name__ == "__main__":
    main()
