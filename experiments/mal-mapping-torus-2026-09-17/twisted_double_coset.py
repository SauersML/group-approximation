"""Search for n in F_2=<a,b> outside <a> with phi^q(n) in <a> n <a>, q>=1,
where phi(a)=a, phi(b)=b a b^-2 is the stage endomorphism of Gamma_mal
(G = <a,b,t | t^-1 a t = a, t^-1 b t = b a b^-2>, t^-1 x t = phi(x)).

Such n (with q) are exactly the extra generators g = n t^m of the q-normal
step Z^2=<a,t> -> <g : g Z^2 g^-1 cap Z^2 infinite> (see Lemma 1 of the artifact
research/artifacts/fpbs-mal-mapping-torus-2026-09-18.md).
Run: python3 twisted_double_coset.py 10 4   ->  0 solutions (September 18, 2026).
Letters: a=1, A=-1, b=2, B=-2.
"""
import itertools, sys


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


PHI = {1: [1], -1: [-1], 2: [2, 1, -2, -2], -2: [2, 2, -1, -2]}


def phi(w):
    r = []
    for x in w:
        r += PHI[x]
    return red(r)


def strip_a(w):
    w = list(w)
    while w and abs(w[0]) == 1:
        w.pop(0)
    while w and abs(w[-1]) == 1:
        w.pop()
    return w


def main(maxlen=10, maxq=4):
    found = []
    letters = [1, -1, 2, -2]
    for n_len in range(1, maxlen + 1):
        for w in itertools.product(letters, repeat=n_len):
            w = list(w)
            if red(w) != w or abs(w[0]) == 1 or abs(w[-1]) == 1:
                continue
            v = w
            for q in range(1, maxq + 1):
                v = phi(v)
                if strip_a(v) == w:
                    found.append((w, q))
        print(n_len, len(found), flush=True)
    print("solutions:", found[:20])


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 10,
         int(sys.argv[2]) if len(sys.argv) > 2 else 4)
