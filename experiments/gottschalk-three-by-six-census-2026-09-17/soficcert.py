#!/usr/bin/env python3
"""Sofic certificates for census CANDIDATE records: recognize P(T) as a free product of known sofic pieces.

If the table group P(T) is sofic, no strict pair lives on T, whatever its reverse table
(strict-automata-live-on-canonical-table-groups plus sofic-groups-are-surjunctive).

Per CANDIDATE record:
  1. build the relators of P(T) over generators 1..ns-1+nm-1 (x_s for s != 1, then x_m for m != 1);
  2. eliminate generators by Tietze moves (a relator in which a generator occurs exactly once is solved for it),
     logging every move so that verify_sofic.py can replay it;
  3. split the reduced presentation into free factors (connected components of "occur in a common relator"),
     plus a free group on the unused generators;
  4. certify each factor:
       cyclic               one generator (Z or Z/n);
       partially-positive   one relator in which some generator occurs with one sign only
                            (partially-positive-one-relator-groups-are-sofic);
       peelable-extreme     one relator on two generators, not a proper power, whose Magnus rewriting, after
                            Nielsen moves making one exponent sum zero, has a peelable extreme letter
                            (peelable-extreme-one-relator-groups-are-sofic);
       BS(p,q)              recorded additionally when the relator is a b^p a^-1 b^q up to rotation and inversion.
     Free products of sofic groups are sofic (elek-szabo-sofic-permanence).
A record whose every factor is certified becomes SOFIC; other records stay CANDIDATE with the reduced presentation.

Usage: soficcert.py ns nm in.jsonl out.jsonl
"""
import json
import sys


def inv(w):
    return [-x for x in reversed(w)]


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def cyc_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def substitute(w, g, val):
    out = []
    for x in w:
        if x == g:
            out += val
        elif x == -g:
            out += inv(val)
        else:
            out.append(x)
    return free_reduce(out)


def tietze_logged(ngen, relators):
    defs = {g: [g] for g in range(1, ngen + 1)}
    rels = [q for q in (cyc_reduce(r) for r in relators) if q]
    log = []
    changed = True
    while changed:
        changed = False
        for idx, r in enumerate(rels):
            counts = {}
            for x in r:
                counts[abs(x)] = counts.get(abs(x), 0) + 1
            cand = [g for g, c in counts.items() if c == 1]
            if not cand:
                continue
            g = cand[0]
            i = [k for k, x in enumerate(r) if abs(x) == g][0]
            rot = r[i:] + r[:i]
            val = inv(rot[1:]) if rot[0] > 0 else rot[1:]
            log.append([g, idx])
            for h in defs:
                defs[h] = substitute(defs[h], g, val)
            rels = [q for q in (cyc_reduce(substitute(q, g, val)) for k, q in enumerate(rels) if k != idx) if q]
            changed = True
            break
    remaining = sorted({abs(x) for h in defs for x in defs[h]})
    return log, defs, remaining, rels


def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def bs_form(r):
    for w in rotations(r) + rotations(inv(r)):
        if len(w) < 4:
            continue
        a = w[0]
        try:
            k = w.index(-a, 1)
        except ValueError:
            continue
        mid, tail = w[1:k], w[k + 1:]
        if not mid or not tail or abs(mid[0]) == abs(a):
            continue
        b = abs(mid[0])
        if any(abs(x) != b for x in mid + tail) or len(set(mid)) != 1 or len(set(tail)) != 1:
            continue
        return [a, b, len(mid) * (1 if mid[0] > 0 else -1), len(tail) * (1 if tail[0] > 0 else -1)]
    return None


def proper_power(w):
    n = len(w)
    return any(n % d == 0 and w == w[:d] * (n // d) for d in range(1, n))


def partially_positive(w):
    return any((x in w) != (-x in w) for x in {abs(y) for y in w})


def expsum(w, g):
    return sum(1 if x == g else -1 if x == -g else 0 for x in w)


def peelable(w, a, t):
    """w over generators a, t, cyclically reduced, exponent sum of t zero. Test a peelable extreme letter."""
    h = 0
    letters = []
    for x in w:
        if abs(x) == t:
            h += 1 if x > 0 else -1
        else:
            letters.append((h, 1 if x > 0 else -1))
    heights = [q[0] for q in letters]
    m, n = min(heights), max(heights)
    if m == n:
        return False
    for ext in (m, n):
        k = len(letters)
        start = next(i for i in range(k) if letters[i][0] != ext)
        runs, cur = [], 0
        for j in range(k):
            q = letters[(start + j) % k]
            if q[0] == ext:
                cur += q[1]
            elif cur:
                runs.append(cur)
                cur = 0
        if cur:
            runs.append(cur)
        if len(runs) == 1 or (len(runs) == 2 and abs(runs[0]) == abs(runs[1])):
            return True
    return False


def nielsen_zero(w, a, b):
    """Nielsen moves (old b = new b a^k, or old a = new a b^k) until an exponent sum is zero.

    Returns (word, a, t) with t of exponent sum zero, or None."""
    for _ in range(64):
        w = cyc_reduce(w)
        ea, eb = expsum(w, a), expsum(w, b)
        if eb == 0:
            return w, a, b
        if ea == 0:
            return w, b, a
        if abs(ea) >= abs(eb):
            k = -int(ea / eb)  # exponent sum of a becomes ea + k eb, of absolute value < |eb|
            w = substitute(w, b, [b] + ([a] * k if k > 0 else [-a] * (-k)))
        else:
            k = -int(eb / ea)
            w = substitute(w, a, [a] + ([b] * k if k > 0 else [-b] * (-k)))
    return None


def certify_factor(gens, rels):
    if len(gens) == 1:
        return {"cert": "cyclic"}
    if len(rels) != 1:
        return None
    w = rels[0]
    if partially_positive(w):
        c = {"cert": "partially-positive"}
    elif len(gens) == 2 and not proper_power(w):
        nz = nielsen_zero(w, gens[0], gens[1])
        if nz is None or not peelable(*nz):
            return None
        c = {"cert": "peelable-extreme", "nielsen_word": nz[0], "a": nz[1], "t": nz[2]}
    else:
        return None
    bs = bs_form(w) if len(gens) == 2 else None
    if bs:
        c["bs"] = bs
    return c


def factors(remaining, rels):
    parent = {g: g for g in remaining}

    def find(g):
        while parent[g] != g:
            parent[g] = parent[parent[g]]
            g = parent[g]
        return g
    for r in rels:
        gs = sorted({abs(x) for x in r})
        for g in gs[1:]:
            parent[find(g)] = find(gs[0])
    comp = {}
    for r in rels:
        comp.setdefault(find(abs(r[0])), []).append(r)
    used = {abs(x) for r in rels for x in r}
    out = []
    for root, rs in comp.items():
        gens = sorted({abs(x) for r in rs for x in r})
        out.append((gens, rs))
    return out, [g for g in remaining if g not in used]


def main():
    ns, nm, fin, fout = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    stats, certs = {}, {}
    ng = ns - 1 + nm - 1
    with open(fin) as fi, open(fout, "w") as fh:
        for line in fi:
            r = json.loads(line)
            if r["status"] != "CANDIDATE":
                continue
            relators = [[a // 2 + 1 for a in u] + inv([a // 2 + 1 for a in v]) for (u, v) in r["rels"]]
            log, defs, rem, rels = tietze_logged(ng, relators)
            facs, free = factors(rem, rels)
            fc = []
            for gens, rs in facs:
                c = certify_factor(gens, rs)
                if c is None:
                    fc = None
                    break
                c.update({"gens": gens, "relators": rs})
                fc.append(c)
            info = {"log": log, "defs": {str(k): v for k, v in defs.items()}, "remaining": rem, "relators": rels}
            if fc is not None:
                r["status"] = "SOFIC"
                info.update({"factors": fc, "free": free})
                r["sofic"] = info
                key = "+".join(sorted(c["cert"] for c in fc)) or "free"
                certs[key] = certs.get(key, 0) + 1
            else:
                r["tietze"] = info
            stats[r["status"]] = stats.get(r["status"], 0) + 1
            fh.write(json.dumps(r) + "\n")
    print(ns, nm, fin, stats, certs, flush=True)


if __name__ == "__main__":
    main()
