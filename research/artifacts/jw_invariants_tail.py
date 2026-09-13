from fractions import Fraction
v0 = SOLV_hold[0]
A, B, X, Y = mats(v0)
G = {"a": A, "b": B, "x": X, "y": Y, "A": inv(A), "B": inv(B), "X": inv(X), "Y": inv(Y)}
random.seed(5)
worst = 0.0
seen = {}
for t in range(3000):
    L_ = random.randint(1, 8)
    wd = "".join(random.choice("abxyABXY") for _ in range(L_))
    M = (1, 0, 0, 1)
    for ch in wd:
        M = mm(M, G[ch])
    t2 = (M[0] + M[3]) ** 2
    fr = Fraction(t2.real).limit_denominator(10**4)
    err = abs(t2 - complex(fr))
    worst = max(worst, err)
    den = fr.denominator
    seen[den] = seen.get(den, 0) + 1
print("max distance of tr^2 from a rational with denominator <= 10^4:", worst)
print("denominators observed (count):", sorted(seen.items())[:20])
print("solution entries:", ["%.12f%+.12fi" % (z.real, z.imag) for z in v0])
print("DONE3")
