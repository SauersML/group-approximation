#!/usr/bin/env python3
"""Search for a C'(1/6) presentation <x, y | R1, R2, R3> with
R1 a positive word in {x, y}, R2 a positive word in the tokens {x, Yx},
R3 a positive word in the tokens {y, Xy}  (X = x^-1, Y = y^-1).
Each relator uses both of its tokens.  Exact piece computation over the
symmetrized closure.  Letters: x=1, X=-1, y=2, Y=-2.
"""
import itertools, json, random, sys

def reduce(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out

def cyclically_reduced(w):
    return len(w) > 0 and w[0] != -w[-1] and reduce(w) == w

def inverse(w):
    return [-a for a in reversed(w)]

def primitive(w):
    n = len(w)
    for d in range(1, n):
        if n % d == 0 and w == w[d:] + w[:d]:
            return False
    return True

def symmetrized(rels):
    S = []
    for r in rels:
        for s in (r, inverse(r)):
            for i in range(len(s)):
                S.append(tuple(s[i:] + s[:i]))
    return S

def max_piece_ratio(rels):
    S = symmetrized(rels)
    worst = 0.0
    worst_pair = None
    n = len(S)
    for i in range(n):
        r = S[i]
        for j in range(n):
            if i == j:
                continue
            s = S[j]
            if r == s:
                return float('inf'), (r, s, len(r))
            L = min(len(r), len(s))
            k = 0
            while k < L and r[k] == s[k]:
                k += 1
            ratio = k / len(r)
            if ratio > worst:
                worst, worst_pair = ratio, (r, s, k)
    return worst, worst_pair

def r1_word(exps):
    w = []
    for e, f in exps:
        w += [1] * e + [2] * f
    return w

def r2_word(exps):
    w = []
    for e, f in exps:
        w += [1] * e + [-2, 1] * f
    return w

def r3_word(exps):
    w = []
    for e, f in exps:
        w += [2] * e + [-1, 2] * f
    return w

def tokens_used(exps):
    return any(e > 0 for e, _ in exps) and any(f > 0 for _, f in exps)

def random_exps(k, lo, hi, rng):
    return [(rng.randint(lo, hi), rng.randint(lo, hi)) for _ in range(k)]

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    rng = random.Random(seed)
    best = None
    for t in range(trials):
        e1, e2, e3 = (random_exps(k, 1, 4, rng) for _ in range(3))
        rels = [r1_word(e1), r2_word(e2), r3_word(e3)]
        if not all(cyclically_reduced(r) and primitive(r) for r in rels):
            continue
        ratio, pair = max_piece_ratio(rels)
        if best is None or ratio < best[0]:
            best = (ratio, e1, e2, e3, pair)
            print(f"trial {t}: max piece ratio {ratio:.4f} lengths {[len(r) for r in rels]}", flush=True)
            if ratio < 1 / 6:
                break
    ratio, e1, e2, e3, pair = best
    out = {
        "seed": seed, "k": k, "max_piece_ratio": ratio,
        "C_prime_one_sixth": ratio < 1 / 6,
        "R1_syllables_x_y": e1, "R2_syllables_x_Yx": e2, "R3_syllables_y_Xy": e3,
        "lengths": [len(r1_word(e1)), len(r2_word(e2)), len(r3_word(e3))],
        "worst_piece_len": pair[2],
    }
    print(json.dumps(out))

if __name__ == "__main__":
    main()
