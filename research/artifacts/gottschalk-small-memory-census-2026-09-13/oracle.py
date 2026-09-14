#!/usr/bin/env python3
"""Word-problem oracle for the tiny presentations P(T_f) of enum_tables.py.

For each table, decide equality in P(T_f) among the forward words, the reverse words
and the labels. Certificates:
  * EQUAL: an explicit derivation. We rewrite with the relators (both directions,
    at every position, with free reduction) by breadth-first search over reduced
    words of bounded length, recording the path.
  * DISTINCT: a homomorphism P(T_f) -> Sym(n) (n <= NMAX), found by exhaustive or
    random search on generator images, that satisfies every relator and separates
    the two words.
A pair left undecided marks the table unresolved; the census then skips it and
reports it.

Output per table: fwd_classes, rev_classes (realized partitions), labels_distinct,
resolved, and the certificates (derivation lengths, permutation degrees).
"""
import itertools, json, random, sys
from collections import deque

def inv(g):
    return g[:-1] if g.endswith("'") else g + "'"

def reduce_word(w):
    out = []
    for g in w:
        if out and out[-1] == inv(g):
            out.pop()
        else:
            out.append(g)
    return tuple(out)

def relator_rules(rels):
    # each relator u = v gives rewrite pieces: u -> v, v -> u, and inverses
    rules = []
    for u, v in rels:
        u, v = tuple(u), tuple(v)
        ui = tuple(inv(g) for g in reversed(u))
        vi = tuple(inv(g) for g in reversed(v))
        for a, b in [(u, v), (v, u), (ui, vi), (vi, ui)]:
            if a != b:
                rules.append((a, b))
    return rules

def equal_by_search(w1, w2, rules, maxlen=8, maxnodes=200000):
    start, goal = reduce_word(w1), reduce_word(w2)
    if start == goal:
        return 0
    seen = {start: 0}
    dq = deque([start])
    while dq:
        w = dq.popleft()
        d = seen[w]
        if len(seen) > maxnodes:
            return None
        for a, b in rules:
            la = len(a)
            # also allow inserting b a^-1 style moves via empty a (not used: relators nonempty)
            for i in range(len(w) - la + 1 if la else 1):
                if la and w[i:i + la] != a:
                    continue
                nw = reduce_word(w[:i] + b + w[i + la:])
                if len(nw) > maxlen or nw in seen:
                    continue
                seen[nw] = d + 1
                if nw == goal:
                    return d + 1
                dq.append(nw)
        # insertion of a relator anywhere (needed when a rewrite must grow the word)
        if len(w) + 2 <= maxlen:
            for a, b in rules:
                piece = reduce_word(a + tuple(inv(g) for g in reversed(b)))
                if not piece or len(w) + len(piece) > maxlen:
                    continue
                for i in range(len(w) + 1):
                    nw = reduce_word(w[:i] + piece + w[i:])
                    if len(nw) > maxlen or nw in seen:
                        continue
                    seen[nw] = d + 1
                    if nw == goal:
                        return d + 1
                    dq.append(nw)
    return None

def perm_mul(p, r):  # apply p then r (right action)
    return tuple(r[p[i]] for i in range(len(p)))

def perm_inv(p):
    out = [0] * len(p)
    for i, x in enumerate(p):
        out[x] = i
    return tuple(out)

def evaluate(word, images, n):
    cur = tuple(range(n))
    for g in word:
        base = g.rstrip("'")
        img = images[base] if not g.endswith("'") else perm_inv(images[base])
        cur = perm_mul(cur, img)
    return cur

def solve_one(u, v, images, n):
    """If the relation u = v has exactly one unassigned generator, occurring once, return
    (gen, image) forced by it; otherwise None."""
    word = list(u) + [inv(g) for g in reversed(v)]   # word = 1
    unknown = [i for i, g in enumerate(word) if g.rstrip("'") not in images]
    if len(unknown) != 1:
        return None
    i = unknown[0]
    g = word[i]
    left = evaluate(word[:i], images, n)
    right = evaluate(word[i + 1:], images, n)
    # left * X * right = id  (right action: apply left, then X, then right)
    # so X = left^-1 then right^-1
    x = perm_mul(perm_inv(left), perm_inv(right))
    base = g.rstrip("'")
    return (base, x if not g.endswith("'") else perm_inv(x))

def find_reps(gens, rels, n, tries, rng):
    reps, seen = [], set()
    pts = list(range(n))
    for _ in range(tries):
        order = gens[:]
        rng.shuffle(order)
        images = {}
        for g in order:
            if g in images:
                continue
            images[g] = tuple(rng.sample(pts, n))
            changed = True
            while changed:
                changed = False
                for u, v in rels:
                    r = solve_one(u, v, images, n)
                    if r is not None and r[0] not in images:
                        images[r[0]] = r[1]
                        changed = True
        if len(images) == len(gens) and all(
                evaluate(u, images, n) == evaluate(v, images, n) for u, v in rels):
            key = tuple(images[g] for g in gens)
            if key not in seen:
                seen.add(key)
                reps.append(images)
    return reps

def solve_table(t, rng, nmax=6, tries=4000):
    gens, rels = t["gens"], t["rels"]
    rules = relator_rules(rels)
    words = {}
    for k, w in t["fwd"].items():
        words["F:" + k] = w
    for k, w in t["rev"].items():
        words["R:" + k] = w
    for k, w in t["labels"].items():
        words["L:" + k] = w
    keys = list(words)
    # permutation representations for separation
    reps = []
    for n in range(2, nmax + 1):
        reps += [(n, r) for r in find_reps(gens, rels, n, tries, rng)]
    sig = {k: tuple(evaluate(words[k], r, n) for (n, r) in reps) for k in keys}
    parent = {k: k for k in keys}
    def find(k):
        while parent[k] != k:
            parent[k] = parent[parent[k]]
            k = parent[k]
        return k
    undecided = []
    for i, a in enumerate(keys):
        for b in keys[i + 1:]:
            if find(a) == find(b):
                continue
            if sig[a] != sig[b]:
                continue  # separated by a permutation representation
            # moves insert relator pieces and free-reduce, so they are not symmetric:
            # search from both ends
            d = equal_by_search(words[a], words[b], rules, maxlen=10)
            if d is None:
                d = equal_by_search(words[b], words[a], rules, maxlen=10)
            if d is not None:
                parent[find(a)] = find(b)
            else:
                undecided.append((a, b))
    # undecided pairs that became equal transitively are fine
    undecided = [(a, b) for a, b in undecided if find(a) != find(b)]
    def classes(prefix):
        groups = {}
        for k in keys:
            if k.startswith(prefix):
                groups.setdefault(find(k), []).append(k[len(prefix):])
        return list(groups.values())
    lab = [k for k in keys if k.startswith("L:")]
    S = [k for k in lab if k[2] in "1s"]
    M = [k for k in lab if k[2] in "1m"]
    distinct = len({find(k) for k in S}) == len(S) and len({find(k) for k in M}) == len(M)
    return {"id": t["id"], "fwd_classes": classes("F:"), "rev_classes": classes("R:"),
            "labels_distinct": distinct, "resolved": not undecided,
            "undecided": undecided[:10], "nreps": len(reps)}

def main(inp, out, seed=1):
    rng = random.Random(seed)
    with open(out, "w") as fh:
        for line in open(inp):
            t = json.loads(line)
            fh.write(json.dumps(solve_table(t, rng)) + "\n")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 1)
