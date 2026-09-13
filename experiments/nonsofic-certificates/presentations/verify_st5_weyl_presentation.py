#!/usr/bin/env python3
"""A seven-generator, sixty-relator presentation of the binary Leavitt unit group, checked exactly.

L = L_{F_2}(1,2), G = L^x.  Chart D = (00, 01, 10, 110, 111) and the ring isomorphism
Theta : M_5(L) -> L, Theta(M) = sum_ij S[d_i] M_ij T[d_j], so GL_5(L) = G and
Theta(E_ij(r)) = 1 + S[d_i] r T[d_j].

Generators and their images in G:
  c   = Theta(P_(12345))   the Thompson unit d_k w -> d_(k+1) w
  t   = Theta(P_(12))      the Thompson unit swapping d_1 and d_2
  y_a = Theta(E_12(a))     a in {1, e, f, E, F} = {1, s0, s1, t0, t1}

For a root (i,j), X_ij(a) = p y_a p^-1, p the shortest word in c, c^-1, t whose permutation
sends 1 -> i, 2 -> j.  Commutators are [x,y] = x y x^-1 y^-1.

What is checked:
 1. every relator of the presentation evaluates to 1 in G (dual normal-form/prefix-table mode);
 2. coset enumeration: the five W relators present a group of order 120 (so S_5);
 3. every X-word equals Theta(E_ij(a)), for all six permutations p sending (1,2) to (i,j);
 4. control: the full Steinberg family (A)(B)(P2)(CK)(unit)(partition)(D) at every root;
 5. negative controls.
"""
import collections
import hashlib
import itertools
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get("CERT_DIR", os.path.dirname(HERE)))
import leavitt as Lv  # noqa: E402

D = ["00", "01", "10", "110", "111"]
LETTERS = ["1", "e", "f", "E", "F"]
RING = {"1": Lv.ONE, "e": Lv.s0, "f": Lv.s1, "E": Lv.t0, "F": Lv.t1}
PRODUCT = {("E", "e"): "1", ("F", "f"): "1", ("E", "f"): "0", ("F", "e"): "0"}
for _a in LETTERS:
    PRODUCT[("1", _a)] = _a
    PRODUCT[(_a, "1")] = _a
IRREDUCIBLE = [(a, b) for a in LETTERS for b in LETTERS if (a, b) not in PRODUCT]
PERM = {"c": (1, 2, 3, 4, 0), "t": (1, 0, 2, 3, 4)}


def inv(word):
    return [(g, -e) for g, e in reversed(word)]


def reduce(word):
    out = []
    for g, e in word:
        if out and out[-1] == (g, -e):
            out.pop()
        else:
            out.append((g, e))
    return out


def comm(x, y):
    return reduce(x + y + inv(x) + inv(y))


def render(word):
    return " ".join(g if e == 1 else g + "^-1" for g, e in word) or "1"


def perm_of(word):
    sigma = tuple(range(5))
    for g, e in word:
        p = PERM[g]
        if e == -1:
            p = tuple(sorted(range(5), key=lambda i: p[i]))
        sigma = tuple(sigma[p[i]] for i in range(5))
    return sigma


def weyl_words():
    best = {tuple(range(5)): []}
    queue = collections.deque([[]])
    while queue:
        w = queue.popleft()
        for step in (("c", 1), ("c", -1), ("t", 1)):
            w2 = w + [step]
            s = perm_of(w2)
            if s not in best:
                best[s] = w2
                queue.append(w2)
    return best


WEYL = weyl_words()


def root_conj(i, j):
    cands = [(len(w), k, w) for k, (s, w) in enumerate(WEYL.items()) if s[0] == i and s[1] == j]
    return min(cands)[2]


def X(i, j, a, conj=None):
    p = root_conj(i, j) if conj is None else conj
    return reduce(p + [("y" + a, 1)] + inv(p))


def theta_E(i, j, r):
    return Lv.one_plus_nilpotent(Lv.S(D[i]) * r * Lv.T(D[j]))


def perm_unit(sigma):
    return Lv.thompson_unit(D, [D[sigma[k]] for k in range(5)])


UNITS = {"c": perm_unit(PERM["c"]), "t": perm_unit(PERM["t"])}
for _a in LETTERS:
    UNITS["y" + _a] = theta_E(0, 1, RING[_a])


def evaluate(word):
    u = Lv.IDENTITY
    for g, e in word:
        u = u * (UNITS[g] if e == 1 else UNITS[g].inverse())
    return u


def presentation():
    rels = []

    def add(family, name, word):
        rels.append((family, name, reduce(word)))

    c, C, t = [("c", 1)], [("c", -1)], [("t", 1)]

    def y(a):
        return [("y" + a, 1)]

    add("W", "t^2", t * 2)
    add("W", "c^5", c * 5)
    add("W", "(tc)^4", (t + c) * 4)
    add("W", "(t c^-1 t c)^3", (t + C + t + c) * 3)
    add("W", "(t c^-2 t c^2)^2", (t + C + C + t + c + c) * 2)
    s34, s45 = c + c + t + C + C, C + C + t + c + c
    for a in LETTERS:
        add("K", "[y%s, (34)]" % a, comm(y(a), s34))
        add("K", "[y%s, (45)]" % a, comm(y(a), s45))
    add("L", "(t y1)^3", (t + y("1")) * 3)
    add("D", "y1^2", y("1") * 2)
    for a, b in itertools.combinations_with_replacement(LETTERS, 2):
        add("B", "[X12(%s), X34(%s)]" % (a, b), comm(X(0, 1, a), X(2, 3, b)))
    add("B", "[X12(1), X13(1)]", comm(X(0, 1, "1"), X(0, 2, "1")))
    add("B", "[X12(1), X32(1)]", comm(X(0, 1, "1"), X(2, 1, "1")))
    for (a, b), prod in PRODUCT.items():
        rhs = [] if prod == "0" else X(0, 2, prod)
        add("C", "[X12(%s), X23(%s)] = X13(%s)" % (a, b, prod),
            comm(X(0, 1, a), X(1, 2, b)) + inv(rhs))
    for a, b in IRREDUCIBLE:
        add("P", "[X12(%s), X23(%s)] = [X14(%s), X43(%s)]" % (a, b, a, b),
            comm(X(0, 1, a), X(1, 2, b)) + inv(comm(X(0, 3, a), X(3, 2, b))))
    add("Q", "[X12(e), X23(E)] [X12(f), X23(F)] = X13(1)",
        comm(X(0, 1, "e"), X(1, 2, "E")) + comm(X(0, 1, "f"), X(1, 2, "F")) + inv(X(0, 2, "1")))
    return rels


def todd_coxeter(ngens, relators, limit=100000):
    """HLT coset enumeration over the trivial subgroup (Holt-Eick-O'Brien, Section 5.1)."""
    n2 = 2 * ngens

    def iv(x):
        return (x + ngens) % n2

    table, parent, queue = [[None] * n2], [0], []

    def rep(k):
        root = k
        while parent[root] != root:
            root = parent[root]
        while parent[k] != root:
            parent[k], k = root, parent[k]
        return root

    def merge(k, l):
        k, l = rep(k), rep(l)
        if k != l:
            k, l = min(k, l), max(k, l)
            parent[l] = k
            queue.append(l)

    def coincidence(a, b):
        del queue[:]
        merge(a, b)
        i = 0
        while i < len(queue):
            g = queue[i]
            i += 1
            for x in range(n2):
                d = table[g][x]
                if d is not None:
                    table[d][iv(x)] = None
                    mu, nu = rep(g), rep(d)
                    if table[mu][x] is not None:
                        merge(nu, table[mu][x])
                    elif table[nu][iv(x)] is not None:
                        merge(mu, table[nu][iv(x)])
                    else:
                        table[mu][x], table[nu][iv(x)] = nu, mu

    def define(a, x):
        if len(table) >= limit:
            raise RuntimeError("coset limit")
        table.append([None] * n2)
        parent.append(len(parent))
        b = len(table) - 1
        table[a][x], table[b][iv(x)] = b, a

    def scan_and_fill(a, w):
        f, b, i, j = a, a, 0, len(w) - 1
        while True:
            while i <= j and table[f][w[i]] is not None:
                f, i = table[f][w[i]], i + 1
            if i > j:
                if f != b:
                    coincidence(f, b)
                return
            while j >= i and table[b][iv(w[j])] is not None:
                b, j = table[b][iv(w[j])], j - 1
            if j < i:
                coincidence(f, b)
                return
            if i == j:
                table[f][w[i]], table[b][iv(w[i])] = b, f
                return
            define(f, w[i])

    a = 0
    while a < len(table):
        for w in relators:
            if parent[a] != a:
                break
            scan_and_fill(a, w)
        if parent[a] == a:
            for x in range(n2):
                if table[a][x] is None:
                    define(a, x)
        a += 1
    live = [k for k in range(len(table)) if parent[k] == k]
    index = {k: n for n, k in enumerate(live)}
    perms = [[index[rep(table[k][x])] for k in live] for x in range(n2)]
    return len(live), perms


def main():
    t0 = time.time()
    Lv.set_dual(True)
    out = {"chart": D, "generators": {g: Lv.render(u.val) for g, u in UNITS.items()}}
    rels = presentation()
    fails = [name for fam, name, w in rels if not evaluate(w).is_identity()]
    out["relators"] = [{"family": fam, "name": name, "word": render(w), "length": len(w)}
                       for fam, name, w in rels]
    out["relator_count"] = len(rels)
    out["family_counts"] = dict(collections.Counter(fam for fam, _n, _w in rels))
    out["total_length"] = sum(len(w) for _f, _n, w in rels)
    out["max_length"] = max(len(w) for _f, _n, w in rels)
    out["relators_failing_in_G"] = fails
    blob = "\n".join(render(w) for _f, _n, w in rels).encode()
    out["relator_sha256"] = hashlib.sha256(blob).hexdigest()
    code = {"c": 0, "t": 1}
    wr = []
    for fam, _n, w in rels:
        if fam == "W":
            wr.append([code[g] if e == 1 else code[g] + 2 for g, e in w])
    order, perms = todd_coxeter(2, wr)
    ok_perm = all(sorted(p) == list(range(order)) for p in perms)
    out["weyl_presented_order"] = order
    out["weyl_table_is_permutation_rep"] = ok_perm
    out["weyl_words_found"] = len(WEYL)
    bad_perm = [s for s, w in WEYL.items() if evaluate(w) != perm_unit(s)]
    out["weyl_word_image_mismatches"] = len(bad_perm)
    E = {(i, j, a): theta_E(i, j, RING[a])
         for i in range(5) for j in range(5) if i != j for a in LETTERS}
    bad_x = []
    for s, w in WEYL.items():
        for a in LETTERS:
            if evaluate(X(s[0], s[1], a, conj=w)) != E[s[0], s[1], a]:
                bad_x.append((s, a))
    out["x_word_checks"] = 120 * 5
    out["x_word_mismatches"] = len(bad_x)

    def cm(x, y):
        return x * y * x.inverse() * y.inverse()

    roots = [(i, j) for i in range(5) for j in range(5) if i != j]
    ctrl = collections.Counter()
    ctrl_fail = collections.Counter()
    for (i, j), (k, l) in itertools.product(roots, repeat=2):
        if i != l and k != j:
            for a, b in itertools.product(LETTERS, repeat=2):
                ctrl["A+B"] += 1
                ctrl_fail["A+B"] += not cm(E[i, j, a], E[k, l, b]).is_identity()
    for i, j, k in itertools.permutations(range(5), 3):
        for a, b in itertools.product(LETTERS, repeat=2):
            ctrl["St3 (P2, CK, unit)"] += 1
            ctrl_fail["St3 (P2, CK, unit)"] += cm(E[i, j, a], E[j, k, b]) != theta_E(i, k, RING[a] * RING[b])
        ctrl["partition"] += 1
        ctrl_fail["partition"] += not (cm(E[i, j, "e"], E[j, k, "E"]) * cm(E[i, j, "f"], E[j, k, "F"])
                                       * E[i, k, "1"].inverse()).is_identity()
    for i, j in roots:
        for a in LETTERS:
            ctrl["D"] += 1
            ctrl_fail["D"] += not (E[i, j, a] * E[i, j, a]).is_identity()
    out["family_control_checked"] = dict(ctrl)
    out["family_control_failures"] = dict(ctrl_fail)
    c, C, t = [("c", 1)], [("c", -1)], [("t", 1)]
    neg = {
        "[X12(e), X21(E)] = 1": comm(X(0, 1, "e"), X(1, 0, "E")),
        "(t ye)^3 = 1": (t + [("ye", 1)]) * 3,
        "[ye, (23)] = 1": comm([("ye", 1)], c + t + C),
        "(tc)^3 = 1": (t + c) * 3,
        "[X12(e), X23(E)] = X13(1)": comm(X(0, 1, "e"), X(1, 2, "E")) + inv(X(0, 2, "1")),
        "[X12(e), X23(e)] = [X14(e), X43(f)]": comm(X(0, 1, "e"), X(1, 2, "e")) + inv(comm(X(0, 3, "e"), X(3, 2, "f"))),
    }
    out["negative_controls_nonidentity"] = {k: not evaluate(w).is_identity() for k, w in neg.items()}
    out["dual"] = Lv.dual_stats()
    out["seconds"] = round(time.time() - t0, 1)
    verdict = (not fails and order == 120 and ok_perm and not bad_perm and not bad_x
               and not any(ctrl_fail.values()) and all(out["negative_controls_nonidentity"].values()))
    out["verdict"] = "PASS" if verdict else "FAIL"
    path = os.environ.get("OUT_JSON", os.path.join(HERE, "st5-weyl-presentation.json"))
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    summary = {k: v for k, v in out.items() if k not in ("relators", "generators")}
    print(json.dumps(summary, indent=1))
    for fam, name, w in rels:
        print("%s | %-44s | %3d | %s" % (fam, name, len(w), render(w)))
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
