"""Squaring screen for depth growth of binary Leavitt units.

For a unit u, compute u^(2^k) and u^(-2^k) by repeated squaring, recording
depth, degree range and monomial count.  A unit of infinite order with
lambda(u) > 0 doubles its depth per squaring and hits the cap within a few
steps.  A unit whose depth grows additively per squaring while no repetition
occurs is a candidate for lambda(u) = 0 (sublinear depth growth).

Usage: python3.11 sq_screen.py SEED DRAWS MINLEN MAXLEN K CAP
"""
import random, sys, time
sys.path.insert(0, "/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/"
                   "experiments/nonsofic-certificates")
import leavitt as L
L.set_dual(False)


def depth(e):
    return max((max(len(a), len(b)) for a, b in e.terms), default=0)


def degrange(e):
    ds = [len(a) - len(b) for a, b in e.terms]
    return (min(ds), max(ds)) if ds else (0, 0)


def gens():
    g = {}
    g["A"] = L.thompson_unit(["0", "10", "11"], ["00", "01", "1"])
    g["B"] = L.thompson_unit(["0", "10", "110", "111"], ["0", "100", "101", "11"])
    g["C"] = L.thompson_unit(["0", "10", "11"], ["11", "0", "10"])
    g["P"] = L.thompson_unit(["0", "10", "11"], ["10", "0", "11"])
    nil = {"X": "S[0]T[10]", "Y": "S[10]T[0]", "Z": "S[0]T[1]",
           "W": "S[0]T[11]", "U": "S[11]T[0]", "M": "S[0]T[100]",
           "N": "S[100]T[0]", "Q": "S[01]T[1]", "R": "S[1]T[01]"}
    for k, t in nil.items():
        g[k] = L.one_plus_nilpotent(L.parse_elem(t))
    out = {}
    for k, u in g.items():
        out[k] = (u.val, u.inv)
        out[k.lower()] = (u.inv, u.val)
    return out


def word_unit(word, G):
    val, inv = L.ONE, L.ONE
    for ch in word:
        gv, gi = G[ch]
        val = val * gv
        inv = gi * inv
    return val, inv


def squares(val, inv, K, cap):
    seen = {val.terms: 0}
    rows = [(0, depth(val), depth(inv), degrange(val), degrange(inv), len(val), len(inv))]
    for k in range(1, K + 1):
        if len(val) > cap or len(inv) > cap:
            return "CAP", k - 1, rows
        val = val * val
        inv = inv * inv
        if val.is_one():
            return "FIN2", k, rows
        if val.terms in seen:
            return "REP", (seen[val.terms], k), rows
        seen[val.terms] = k
        rows.append((k, depth(val), depth(inv), degrange(val), degrange(inv), len(val), len(inv)))
    return "OK", K, rows


def main():
    seed, draws, minlen, maxlen, K, cap = map(int, sys.argv[1:7])
    rng = random.Random(seed)
    G = gens()
    letters = sorted(G)
    done = set()
    stats = {}
    t0 = time.time()
    for _ in range(draws):
        n = rng.randint(minlen, maxlen)
        w = "".join(rng.choice(letters) for _ in range(n))
        val, inv = word_unit(w, G)
        if val.terms in done:
            continue
        done.add(val.terms)
        status, info, rows = squares(val, inv, K, cap)
        stats[status] = stats.get(status, 0) + 1
        ds = [max(r[1], r[2]) for r in rows]
        # log-depth candidate: at least 3 squarings recorded, the last three steps each add <= 2
        slow = len(rows) >= 4 and all(ds[i] - ds[i - 1] <= 2 for i in range(len(ds) - 3, len(ds)))
        tag = "SLOW" if (slow and status in ("OK", "CAP")) else "ROW"
        print(tag, w, status, info, "depths", ds,
              "deg", [r[3] for r in rows][-2:], "mono", [r[5] for r in rows][-2:], flush=True)
    print("SUMMARY seed", seed, stats, "time %.1f" % (time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
