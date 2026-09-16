"""Independent re-verification of WEIGHT certificates (does not import vgroup, certify or weighttest).

For each line "<id> <word> WEIGHT theta=<q_0>,...,<q_(n-1)>":
  1. parse the word into syllables g_i t^(e_i) (g_i in 1,a,b,B,c; e_i = +-1), check it is cyclically
     reduced in the census sense (opposite-sign corners carry a letter) and not a proper power,
     and that deg_t(w) != 0;
  2. star graph: corner i (between t^(e_(i-1)) and t^(e_i), label g_i) is an edge
     t^(-e_(i-1)) -> t^(e_i);
  3. check theta_i >= 0, the zero set is at most one non-loop edge, and (WT1) sum (1 - theta_i) >= 2;
  4. enumerate, with an explicit stack, every cyclically reduced closed path of weight < 2 (all start
     vertices and rotations) and prove its label nontrivial in BOTH reading orders by exhibiting a
     binary sequence moved by the element.  The generators act on sequences by prefix replacement;
     a moved point is an exact proof that the element is not the identity.
Any failure rejects the certificate.  Output: counts, and the rejected ids.
"""
import random
import sys
from fractions import Fraction

# prefix maps acting on binary strings; a, c involutions, B = b^-1
MAPS = {
    "a": (("00", "01"), ("01", "00"), ("1", "1")),
    "b": (("00", "00"), ("01", "10"), ("10", "11"), ("11", "01")),
    "B": (("00", "00"), ("10", "01"), ("11", "10"), ("01", "11")),
    "c": (("1", "00"), ("00", "1"), ("01", "01")),
}
INVL = {"a": "a", "b": "B", "B": "b", "c": "c"}


def act(letter, s):
    for d, r in MAPS[letter]:
        if s.startswith(d):
            return r + s[len(d):]
    raise ValueError("point too short")


def moved(letters, pts):
    for p in pts:
        x = p
        for ch in letters:
            x = act(ch, x)
        # x is a prefix of the image of every point with prefix p, and p is a prefix of the point;
        # a disagreement within the common length proves the element moves those points
        L = min(len(x), len(p))
        if x[:L] != p[:L]:
            return True
    return False


def parse(word):
    signs, coeffs, cur = [], [], "1"
    for ch in word:
        if ch in "tT":
            signs.append(1 if ch == "t" else -1)
            coeffs.append(cur)
            cur = "1"
        else:
            assert cur == "1" and ch in MAPS
            cur = ch
    assert cur == "1"
    return signs, coeffs


def main():
    rng = random.Random(1916)
    pts = ["".join(rng.choice("01") for _ in range(200)) for _ in range(12)]
    ok = bad = 0
    rejected = []
    npaths = 0
    for line in open(sys.argv[1]):
        parts = line.split()
        if len(parts) < 4 or parts[2] != "WEIGHT":
            continue
        wid, word = parts[0], parts[1]
        theta = [Fraction(x) for x in parts[3].split("=", 1)[1].split(",")]
        signs, coeffs = parse(word)
        n = len(signs)
        good = len(theta) == n and sum(signs) != 0
        for i in range(n):
            if signs[i - 1] != signs[i] and coeffs[i] == "1":
                good = False
        for d in range(1, n):
            if n % d == 0 and all(signs[i] == signs[(i + d) % n] and coeffs[i] == coeffs[(i + d) % n]
                                  for i in range(n)):
                good = False
        edges = []
        for i in range(n):
            src = "-" if signs[i - 1] > 0 else "+"
            dst = "+" if signs[i] > 0 else "-"
            edges.append((src, dst, coeffs[i]))
        zeros = [i for i in range(n) if theta[i] == 0]
        if min(theta) < 0 or len(zeros) > 1 or any(edges[i][0] == edges[i][1] for i in zeros):
            good = False
        if sum(1 - x for x in theta) < 2:
            good = False
        if good:
            # explicit stack DFS: state (start, vertex, steps tuple, letters string, weight)
            stack = []
            for v0 in "-+":
                stack.append((v0, v0, (), "", Fraction(0)))
            while stack and good:
                v0, v, steps, lab, wt = stack.pop()
                if steps and v == v0:
                    (j0, d0), (jl, dl) = steps[0], steps[-1]
                    if not (j0 == jl and d0 == -dl):
                        npaths += 1
                        if not (moved(lab, pts) and moved(lab[::-1], pts)):
                            good = False
                            break
                for j, (src, dst, g) in enumerate(edges):
                    for d, a, b in ((1, src, dst), (-1, dst, src)):
                        if a != v:
                            continue
                        if steps and steps[-1] == (j, -d):
                            continue
                        nw = wt + theta[j]
                        if nw >= 2:
                            continue
                        letter = "" if g == "1" else (g if d == 1 else INVL[g])
                        stack.append((v0, b, steps + ((j, d),), lab + letter, nw))
        if good:
            ok += 1
        else:
            bad += 1
            rejected.append(wid)
    print("verified", ok, "rejected", bad, "closed paths checked", npaths)
    if rejected:
        print("rejected ids:", " ".join(rejected[:50]))


if __name__ == "__main__":
    main()
