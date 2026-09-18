"""Census of blind binary copy automata over small finite groups.

A blind binary copy rule on an ordered memory M = (m_0, ..., m_{n-1}) is a
perfect matching of the hypercube {0,1}^n: each pattern p is matched to
p xor e_i, and the rule outputs p_i. The automaton is
tau(x)(g) = x(g m_{sel(p_g)}), where p_g is the pattern of x on gM.

For each small group, each memory containing the identity, and each matching
whose selection is not constant (constant selection is a shift), we test
whether tau is bijective on {0,1}^G and whether some configuration has a
non-bijective read map g -> g m_{sel(p_g)}.

Run: python3 experiments/blind-copy-automata-2026-09-17/blind_copy_census.py
"""
import itertools


def matchings(n):
    size = 2 ** n
    res = []

    def rec(match):
        free = [v for v in range(size) if v not in match]
        if not free:
            res.append(dict(match))
            return
        v = free[0]
        for i in range(n):
            w = v ^ (1 << i)
            if w not in match:
                match[v] = i
                match[w] = i
                rec(match)
                del match[v]
                del match[w]

    rec({})
    return res


def cyc(k):
    return list(range(k)), (lambda a, b: (a + b) % k)


def elem2(r):
    return list(range(2 ** r)), (lambda a, b: a ^ b)


def s3():
    els = list(itertools.permutations(range(3)))
    return els, (lambda a, b: tuple(a[b[i]] for i in range(3)))


def is_matching_rule_consistent(mt, n):
    for p, i in mt.items():
        if mt[p ^ (1 << i)] != i:
            return False
    return True


def census(n=3):
    ms = [m for m in matchings(n) if len(set(m.values())) > 1]
    assert all(is_matching_rule_consistent(m, n) for m in ms)
    groups = {
        "Z4": cyc(4), "Z5": cyc(5), "Z6": cyc(6), "Z7": cyc(7),
        "V4": elem2(2), "Z2^3": elem2(3), "S3": s3(),
    }
    out = {}
    for name, (els, mul) in groups.items():
        size = len(els)
        idx = {e: i for i, e in enumerate(els)}
        e = els[0]
        bij = 0
        bij_nonbijective_routing = 0
        examples = []
        for rest in itertools.combinations(els[1:], n - 1):
            mem = (e,) + rest
            for mt in ms:
                images = set()
                routing_defect = False
                injective = True
                for xb in range(2 ** size):
                    x = [(xb >> i) & 1 for i in range(size)]
                    reads = []
                    for g in els:
                        p = sum(x[idx[mul(g, mem[j])]] << j for j in range(n))
                        reads.append(idx[mul(g, mem[mt[p]])])
                    y = tuple(x[h] for h in reads)
                    if len(set(reads)) < size:
                        routing_defect = True
                    if y in images:
                        injective = False
                        break
                    images.add(y)
                if injective:
                    bij += 1
                    if routing_defect:
                        bij_nonbijective_routing += 1
                        if len(examples) < 2:
                            examples.append((mem, sorted(mt.items())))
        out[name] = (bij, bij_nonbijective_routing, examples)
        print(name, "bijective non-shift blind rules:", bij,
              "of which with a non-bijective read map:", bij_nonbijective_routing)
        for ex in examples:
            print("   example memory", ex[0], "matching", ex[1])
    return out


def linear_rules_are_not_blind(nmax=4):
    """No parity rule on n >= 2 addresses is a blind copy rule (brute force)."""
    for n in range(2, nmax + 1):
        ms = matchings(n)
        for sub in range(1, 2 ** n):
            support = [i for i in range(n) if (sub >> i) & 1]
            if len(support) < 2:
                continue
            for mt in ms:
                if all(((p >> mt[p]) & 1) == sum((p >> i) & 1 for i in support) % 2
                       for p in range(2 ** n)):
                    raise AssertionError(("blind linear rule", n, support))
        print("n =", n, ":", len(ms), "perfect matchings; no parity rule of support >= 2 is blind")


def z3_mux_statistics():
    """y(g) = x(g) if x(g-t) = 0 else x(g+t) on Z/3 = {0, t, 2t}."""
    images = set()
    unread = 0
    collide = 0
    total_in = 0
    for xb in range(8):
        x = [(xb >> i) & 1 for i in range(3)]
        reads = [g if x[(g - 1) % 3] == 0 else (g + 1) % 3 for g in range(3)]
        images.add(tuple(x[h] for h in reads))
        indeg0 = sum(1 for h in range(3) if reads.count(h) == 0)
        unread += indeg0
        collide += sum(max(reads.count(h) - 1, 0) for h in range(3))
        total_in += len(reads)
    assert len(images) == 8
    # per-site densities under the uniform measure (average over sites and configurations)
    print("Z/3 mux: bijective; P(site unread) =", unread, "/ 24;",
          "E(N-1)_+ =", collide, "/ 24; E N =", total_in, "/ 24")


def presentation_statistics(els, mul, mem, rule):
    """Enumerate all copy presentations s(p) in {j : p_j = rule(p)} on a finite group and
    return (bijective automaton?, number of presentations, min and max unread density,
    number of presentations with a bijective read map for every x)."""
    n = len(mem)
    size = len(els)
    idx = {e: i for i, e in enumerate(els)}
    pats = list(itertools.product([0, 1], repeat=n))
    opts = [[j for j in range(n) if p[j] == rule(p)] for p in pats]
    assert all(opts), "rule does not fix both constants"
    images = set()
    configs = [[(xb >> i) & 1 for i in range(size)] for xb in range(2 ** size)]
    patmaps = []
    for x in configs:
        row = []
        for g in els:
            row.append(tuple(x[idx[mul(g, mem[j])]] for j in range(n)))
        patmaps.append(row)
        images.add(tuple(rule(p) for p in row))
    bijective = len(images) == 2 ** size
    count = 0
    dens = []
    everywhere_bijective = 0
    for choice in itertools.product(*opts):
        s = dict(zip(pats, choice))
        unread = 0
        allbij = True
        for x, row in zip(configs, patmaps):
            reads = {idx[mul(g, mem[s[p]])] for g, p in zip(els, row)}
            unread += size - len(reads)
            if len(reads) < size:
                allbij = False
        count += 1
        dens.append(unread / (size * len(configs)))
        everywhere_bijective += allbij
    return bijective, count, min(dens), max(dens), everywhere_bijective


if __name__ == "__main__":
    els, mul = elem2(2)  # Klein four group {0, a=1, b=2, ab=3}, xor product
    print("Klein parity x(g)+x(ga)+x(gb): (bijective, presentations, min unread density,"
          " max unread density, presentations with bijective read maps) =",
          presentation_statistics(els, mul, (0, 1, 2), lambda p: sum(p) % 2))
    els3, mul3 = cyc(3)
    print("Z/3 mux on memory (t^-1, 1, t): same statistics =",
          presentation_statistics(els3, mul3, (2, 0, 1), lambda p: p[1] if p[0] == 0 else p[2]))
    print("perfect matchings of Q_3 with nonconstant selection:",
          len([m for m in matchings(3) if len(set(m.values())) > 1]))
    linear_rules_are_not_blind(4)
    z3_mux_statistics()
    census(3)
