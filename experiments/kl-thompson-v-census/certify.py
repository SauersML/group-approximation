"""Exact injectivity certificates for the census words over Thompson's group V.

Input lines: "<id> <word> n=<n> m=<m> r=<r>" from census2.py.  A word is a cyclic sequence of
syllables g_i t^(e_i), e_i = +-1, g_i in {1, a, b, B, c} (Bleak--Quick generators, B = b^-1);
corner i sits between t^(e_(i-1)) and t^(e_i) and carries the label g_i.

Certificate tags, each exact:
  POWER    n = 6 and w = u^k (k >= 2) with u of variable length <= 3 and nonzero degree.
           V -> V_u is injective by kl-length-at-most-five-equations-are-solvable, and
           V -> V_w -> V_u composes to it, so V -> V_w is injective.
  CORNER3  not a proper power, r = 3 light same-sign corners, and (D4), (A2) of
           kl-four-same-sign-corner-words-inject (item 2), checked exactly in V.  Every reduced
           closed path is tested with BOTH product orders of its labels, and loop labels are
           compared with a path label and its inverse, so the test is at least as strict as the
           node's own convention.
  RETRACT  some t0 in V with w^delta(t0) = 1 exactly, delta = delta_k : V -> V the diagonal
           embedding over the complete prefix code P_k (k = |P_k|).  The homomorphism
           V * <t> -> V, g -> delta(g), t -> t0 kills w and restricts to the injective delta on V,
           so V -> V_w is injective.
  FRONTIER none of the above.
Output lines: "<id> <word> <tag> [k=<k> t0=<pairs>]".
Usage: certify.py IN OUT [R] [KS] [LIMIT]
"""
import sys
import random
import time
from itertools import permutations
import vgroup as V

INV = {"a": "a", "b": "B", "B": "b", "c": "c", "1": "1"}
ID = V.identity()
E = {"1": ID, "a": V.GENS["a"], "b": V.GENS["b"], "B": V.GENS["B"], "c": V.GENS["c"]}
PCODES = {1: [""], 2: ["0", "1"], 3: ["0", "10", "11"], 4: ["00", "01", "10", "11"]}


def parse(word):
    signs, coeffs, cur = [], [], "1"
    for ch in word:
        if ch in "tT":
            signs.append(1 if ch == "t" else -1)
            coeffs.append(cur)
            cur = "1"
        else:
            if cur != "1":
                raise ValueError("two letters in one syllable: " + word)
            cur = ch
    if cur != "1":
        raise ValueError("trailing coefficient: " + word)
    return signs, coeffs


def power_period(signs, coeffs):
    n = len(signs)
    for d in range(1, n):
        if n % d == 0 and all(signs[i] == signs[(i + d) % n] and coeffs[i] == coeffs[(i + d) % n]
                              for i in range(n)):
            return d
    return None


def corner_data(signs, coeffs):
    n = len(signs)
    edges, loops = [], {"-": [], "+": []}
    for i in range(n):
        p, c, g = signs[i - 1], signs[i], coeffs[i]
        if p == c:
            edges.append(("P" if c > 0 else "N", g))
        elif p > 0:  # t g t^-1 : loop at t^-
            loops["-"].append(g)
        else:  # t^-1 g t : loop at t^+
            loops["+"].append(g)
    light = []
    for idx, (typ, lab) in enumerate(edges):
        heavy = any(j != idx and ((t2 == typ and l2 == lab) or (t2 != typ and l2 == INV[lab]))
                    for j, (t2, l2) in enumerate(edges))
        if not heavy:
            light.append((typ, lab))
    return edges, loops, light


def ends(typ):
    return ("-", "+") if typ == "P" else ("+", "-")


def closed_paths(light, length, v0):
    out = []

    def rec(v, path):
        if len(path) == length:
            if v == v0:
                out.append(list(path))
            return
        for j, (typ, _) in enumerate(light):
            src, dst = ends(typ)
            for d, a, b in ((1, src, dst), (-1, dst, src)):
                if a != v or (path and path[-1] == (j, -d)):
                    continue
                path.append((j, d))
                rec(b, path)
                path.pop()

    rec(v0, [])
    return out


def products(light, path):
    xs = [E[light[j][1]] if d == 1 else E[light[j][1]].inverse() for j, d in path]
    fwd = ID
    for x in xs:
        fwd = fwd * x
    rev = ID
    for x in reversed(xs):
        rev = rev * x
    return fwd, rev


def corner3(signs, coeffs):
    _, loops, light = corner_data(signs, coeffs)
    if len(light) != 3:
        return False
    for v0 in "-+":
        for path in closed_paths(light, 4, v0):  # (D4)
            if ID in products(light, path):
                return False
        for path in closed_paths(light, 2, v0):  # (A2)
            f, r = products(light, path)
            bad = {f.key(), r.key(), f.inverse().key(), r.inverse().key()}
            for y in loops[v0]:
                if E[y].key() in bad or E[y].inverse().key() in bad:
                    return False
    return True


def ball(radius):
    gens = [E[x] for x in "abBc"]
    seen = {ID.key(): ID}
    frontier = [ID]
    for _ in range(radius):
        nxt = []
        for x in frontier:
            for g in gens:
                y = x * g
                if y.key() not in seen:
                    seen[y.key()] = y
                    nxt.append(y)
        frontier = nxt
    return list(seen.values())


def delta(g, code):
    return V.V({p + d: p + r for p in code for d, r in g.pairs.items()})


def candidates(radius, ks):
    base = ball(radius)
    out = {}
    for k in ks:
        code = PCODES[k]
        seen = {}
        for perm in permutations(code):
            sigma = V.V(dict(zip(code, perm)))
            for x in base:
                t = sigma * x
                seen.setdefault(t.key(), t)
        coeff = {s: delta(E[s], code) for s in E}
        out[k] = (coeff, [(t, t.inverse()) for t in seen.values()])
    return out, len(base)


def retract(signs, coeffs, cands, points):
    for k, (coeff, ts) in cands.items():
        for t, ti in ts:
            seq_ok = True
            for s in points:
                x = s
                try:
                    for g, e in zip(coeffs, signs):
                        if g != "1":
                            x = coeff[g].apply(x)
                        x = (t if e > 0 else ti).apply(x)
                except ValueError:
                    seq_ok = False
                    break
                if x != s:
                    seq_ok = False
                    break
            if not seq_ok:
                continue
            w = ID
            for g, e in zip(coeffs, signs):
                w = w * coeff[g] * (t if e > 0 else ti)
            if w == ID:
                return k, t
    return None


def main():
    inp, outp = sys.argv[1], sys.argv[2]
    radius = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    ks = [int(x) for x in sys.argv[4].split(",")] if len(sys.argv) > 4 else [1, 2, 3, 4]
    limit = int(sys.argv[5]) if len(sys.argv) > 5 else None
    rng = random.Random(20260913)
    points = ["".join(rng.choice("01") for _ in range(96)) for _ in range(3)]
    t0 = time.time()
    cands, nball = candidates(radius, ks) if radius >= 0 else ({}, 0)
    print("ball radius", radius, "size", nball, "candidates", {k: len(v[1]) for k, v in cands.items()},
          "setup_s", round(time.time() - t0, 1), flush=True)
    stats = {}
    t1 = time.time()
    with open(inp) as f, open(outp, "w") as out:
        for i, line in enumerate(f):
            if limit is not None and i >= limit:
                break
            parts = line.split()
            wid, word = parts[0], parts[1]
            signs, coeffs = parse(word)
            tag, extra = "FRONTIER", ""
            d = power_period(signs, coeffs)
            if d is not None and len(signs) == 6 and d <= 3 and sum(signs[:d]) != 0:
                tag = "POWER"
            elif d is None and corner3(signs, coeffs):
                tag = "CORNER3"
            elif cands:
                hit = retract(signs, coeffs, cands, points)
                if hit is not None:
                    tag, extra = "RETRACT", " k=%d t0=%s" % (hit[0], repr(sorted(hit[1].pairs.items())).replace(" ", ""))
            stats[tag] = stats.get(tag, 0) + 1
            out.write("%s %s %s%s\n" % (wid, word, tag, extra))
    print("stats", stats, "words", sum(stats.values()), "loop_s", round(time.time() - t1, 1), flush=True)


if __name__ == "__main__":
    main()
