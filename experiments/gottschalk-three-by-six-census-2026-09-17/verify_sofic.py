#!/usr/bin/env python3
"""Independent check of the SOFIC records written by soficcert.py (pure Python, no imports from the census code).

For each SOFIC record:
  1. rebuild the relators of P(T) from the table relations ("rels", letters 2k -> generator k+1);
  2. replay the logged Tietze moves: at each step the named relator must contain the named generator exactly once;
     solve for it, substitute it everywhere, and drop the relator; the final relators and the substitution words
     must equal the recorded ones;
  3. recompute the free splitting of the reduced presentation and re-check every factor certificate:
       cyclic               the factor has one generator;
       partially-positive   one relator, and some generator of it occurs with one sign only;
       peelable-extreme     one relator on two generators, not a proper power; the recorded Nielsen word is obtained
                            from it by the Nielsen moves b -> b a^k, a -> a b^k (re-derived here), the generator t has
                            exponent sum zero, and the top or bottom Magnus letter forms one syllable or two syllables
                            of equal absolute exponent.
Usage: verify_sofic.py ns nm file.jsonl[.gz] [more ...]
"""
import gzip
import json
import sys


def inv(w):
    return [-x for x in reversed(w)]


def fred(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def cred(w):
    w = fred(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def sub(w, g, val):
    out = []
    for x in w:
        out += val if x == g else inv(val) if x == -g else [x]
    return fred(out)


def replay(ng, relators, log):
    defs = {g: [g] for g in range(1, ng + 1)}
    rels = [q for q in (cred(r) for r in relators) if q]
    for g, idx in log:
        r = rels[idx]
        pos = [k for k, x in enumerate(r) if abs(x) == g]
        if len(pos) != 1:
            return None
        rot = r[pos[0]:] + r[:pos[0]]
        val = inv(rot[1:]) if rot[0] > 0 else rot[1:]
        defs = {h: sub(w, g, val) for h, w in defs.items()}
        rels = [q for q in (cred(sub(q, g, val)) for k, q in enumerate(rels) if k != idx) if q]
    # the eliminated generators must no longer occur
    elim = {g for g, _ in log}
    if any(abs(x) in elim for w in list(defs.values()) + rels for x in w):
        return None
    return defs, rels


def expsum(w, g):
    return sum((x == g) - (x == -g) for x in w)


def zero_expsum(w, a, b):
    for _ in range(64):
        w = cred(w)
        ea, eb = expsum(w, a), expsum(w, b)
        if eb == 0:
            return w, a, b
        if ea == 0:
            return w, b, a
        if abs(ea) >= abs(eb):
            k = -int(ea / eb)
            w = sub(w, b, [b] + [a if k > 0 else -a] * abs(k))
        else:
            k = -int(eb / ea)
            w = sub(w, a, [a] + [b if k > 0 else -b] * abs(k))
    return None


def peel(w, t):
    h, lets = 0, []
    for x in w:
        if abs(x) == t:
            h += 1 if x > 0 else -1
        else:
            lets.append((h, 1 if x > 0 else -1))
    if h != 0:
        return False
    hs = [q[0] for q in lets]
    if min(hs) == max(hs):
        return False
    for ext in (min(hs), max(hs)):
        k = len(lets)
        s = [i for i in range(k) if lets[i][0] != ext][0]
        runs, cur = [], 0
        for j in range(k):
            q = lets[(s + j) % k]
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


def check_factor(c, rs, gens):
    if c["cert"] == "cyclic":
        return len(gens) == 1
    if len(rs) != 1:
        return False
    w = rs[0]
    if c["cert"] == "partially-positive":
        return any((x in w) != (-x in w) for x in gens)
    if c["cert"] == "peelable-extreme":
        n = len(w)
        if len(gens) != 2 or any(n % d == 0 and w == w[:d] * (n // d) for d in range(1, n)):
            return False
        z = zero_expsum(w, gens[0], gens[1])
        return z is not None and z[0] == c["nielsen_word"] and z[2] == c["t"] and peel(z[0], z[2])
    return False


def main():
    ns, nm = int(sys.argv[1]), int(sys.argv[2])
    ng = ns - 1 + nm - 1
    ok = bad = 0
    for f in sys.argv[3:]:
        for line in (gzip.open(f, "rt") if f.endswith(".gz") else open(f)):
            r = json.loads(line)
            if r["status"] != "SOFIC":
                continue
            s = r["sofic"]
            relators = [[a // 2 + 1 for a in u] + inv([a // 2 + 1 for a in v]) for (u, v) in r["rels"]]
            good = all(a % 2 == 0 for (u, v) in r["rels"] for a in u + v)
            rep = replay(ng, relators, s["log"])
            if rep is None or rep[1] != s["relators"] or {str(k): v for k, v in rep[0].items()} != s["defs"]:
                good = False
            else:
                rels = rep[1]
                gens_used = {abs(x) for q in rels for x in q}
                # components
                comp = {}
                for q in rels:
                    comp.setdefault(frozenset(abs(x) for x in q), []).append(q)
                merged = True
                while merged:
                    merged = False
                    keys = list(comp)
                    for i in range(len(keys)):
                        for j in range(i + 1, len(keys)):
                            if keys[i] & keys[j]:
                                comp[keys[i] | keys[j]] = comp.pop(keys[i]) + comp.pop(keys[j])
                                merged = True
                                break
                        if merged:
                            break
                facs = {tuple(sorted(k)): v for k, v in comp.items()}
                rec = {tuple(c["gens"]): c for c in s["factors"]}
                if set(facs) != set(rec) or sorted(s["free"]) != sorted(set(s["remaining"]) - gens_used):
                    good = False
                else:
                    for gens, rs in facs.items():
                        if sorted(map(tuple, rs)) != sorted(map(tuple, rec[gens]["relators"])) or \
                                not check_factor(rec[gens], rs, list(gens)):
                            good = False
            if good:
                ok += 1
            else:
                bad += 1
                print("FAILED", f, r["id"], flush=True)
    print("verified", ok, "failed", bad)


if __name__ == "__main__":
    main()
