"""Independent verifier of finite-quotient certificates for <x, y | r1, r2>.

Input lines: "<id> <r1> <r2> <deg> <img_x> <img_y>", images 1-based comma-separated lists of
length deg (permutation images of the generators).  A line PASSES when:
  - both lists are permutations of 1..deg;
  - evaluating r1 and r2 letter by letter (left to right, applying the generator image
    to the current point; X, Y apply the inverse permutation) returns every point to itself;
  - some generator image moves a point.
Then x, y -> img_x, img_y is a homomorphism G -> Sym(deg) with nontrivial image, i.e. a
nontrivial finite quotient of G.  Usage: verify_certs.py CERTS  (prints counts; exit 1 on FAIL)
"""
import sys


def inv(p):
    q = [0] * len(p)
    for i, v in enumerate(p):
        q[v] = i
    return q


def check(r, gx, gy):
    imgs = {"x": gx, "X": inv(gx), "y": gy, "Y": inv(gy)}
    n = len(gx)
    for start in range(n):
        pt = start
        for c in r:
            pt = imgs[c][pt]
        if pt != start:
            return False
    return True


def main():
    ok = bad = 0
    for ln in open(sys.argv[1]):
        p = ln.split()
        if not p:
            continue
        if len(p) != 6:
            print("FAIL", ln.strip())
            bad += 1
            continue
        _, r1, r2, deg, sx, sy = p
        deg = int(deg)
        gx = [int(v) - 1 for v in sx.split(",")]
        gy = [int(v) - 1 for v in sy.split(",")]
        if len(gx) != deg or len(gy) != deg or sorted(gx) != list(range(deg)) or sorted(gy) != list(range(deg)):
            print("FAIL notperm", p[0])
            bad += 1
            continue
        nontriv = any(v != i for i, v in enumerate(gx)) or any(v != i for i, v in enumerate(gy))
        if check(r1, gx, gy) and check(r2, gx, gy) and nontriv:
            ok += 1
        else:
            print("FAIL relators", p[0])
            bad += 1
    print("PASS %d FAIL %d" % (ok, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
