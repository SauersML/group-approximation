"""Decide pre-injectivity and injectivity of symbol-blind selectors over Z at every alphabet size.

A selector sigma on memory M (a finite subset of Z containing 0, sigma(discrete) = 0) gives
tau_q(x)(n) = x(n + sigma(pi_n x)).  Let w = max M - min M + 1 and s = w - 1.  The pair graph has
states (u, v) in [q]^s x [q]^s and an edge for each pair of new cells (a, b) whose windows ua, vb
give equal outputs.  Nothing depends on the symbols beyond their equality pattern, so we quotient
by permutations of [q]: states are set partitions of the 2s cells with at most q classes, and an
edge appends two cells, each equal to an existing class or fresh, with at most q classes in all.
Quotient paths lift to real paths (choose fresh symbols among the unused ones), and real paths
project, so:
  tau_q is not pre-injective  iff  some path goes diagonal -> off-diagonal -> ... -> diagonal;
  tau_q is not injective      iff  some off-diagonal state lies on a bi-infinite path,
                                   i.e. is reachable from a cycle and reaches a cycle.
For q >= 2s + 2 the class bound never binds, so q = 2..2w decides every q.

Usage: python3 pair_graph_over_z.py fd_sector_results.txt [spec ...]
  For the Z memory blocks of the census file (all, or only the listed specs such as 0,-1,1,2),
  decides each listed rule that passed the finite-defect checks up to defect 2, and every
  e-permutive selector.
"""
import collections
import ast
import itertools
import sys


def canon(t):
    d = {}
    return tuple(d.setdefault(v, len(d)) for v in t)


def set_partitions(n):
    res = [()]
    for _ in range(n):
        res = [p + (c,) for p in res for c in range(max(p, default=-1) + 2)]
    return res


def decide(M, sig, q):
    """sig maps equality patterns (over M in the listed order, 0 first) to memory elements."""
    lo = min(M)
    s = max(M) - lo

    def out(cells):
        vals = tuple(cells[m - lo] for m in M)
        return cells[sig.get(canon(vals), 0) - lo]

    states = [p for p in set_partitions(2 * s) if max(p) + 1 <= q]
    edges = {}
    for st in states:
        k = max(st) + 1
        nxt = set()
        for a in range(k + 1):
            for b in range(max(k, a + 1) + 1):
                if max(k, a + 1, b + 1) > q:
                    continue
                u, v = st[:s] + (a,), st[s:] + (b,)
                if out(u) == out(v):
                    nxt.add(canon(u[1:] + v[1:]))
        edges[st] = nxt

    def diag(st):
        return st[:s] == st[s:]

    frontier = [t for st in states if diag(st) for t in edges[st] if not diag(t)]
    seen, back = set(frontier), False
    while frontier and not back:
        st = frontier.pop()
        for t in edges[st]:
            if diag(t):
                back = True
                break
            if t not in seen:
                seen.add(t)
                frontier.append(t)

    def on_cycles(succ):
        alive = set(states)
        changed = True
        while changed:
            changed = False
            for st in list(alive):
                if not succ[st] & alive:
                    alive.discard(st)
                    changed = True
        return alive

    rev = collections.defaultdict(set)
    for st in states:
        for t in edges[st]:
            rev[t].add(st)
    fwd, bwd = on_cycles(edges), on_cycles(rev)
    inj = not any(not diag(st) and st in fwd and st in bwd for st in states)
    return (not back), inj


def e_permutive(M):
    k = len(M)
    pats = sorted(set(canon(p) for p in itertools.product(range(k), repeat=k)))
    joined = [p for p in pats if p[0] in p[1:]]
    rhos = sorted(set(canon(p[1:]) for p in joined))
    for perms in itertools.product(*[list(itertools.permutations(range(max(r) + 1))) for r in rhos]):
        tau = dict(zip(rhos, perms))
        sig = {}
        for p in joined:
            rho = canon(p[1:])
            j = rho[p[1:].index(p[0])]
            target = tau[rho][j]
            if target != j:
                sig[p] = M[1 + rho.index(target)]
        yield sig


CACHE = {}


def summary(M, sig):
    key = (tuple(M), tuple(sorted(sig.items())))
    if key not in CACHE:
        CACHE[key] = _summary(M, sig)
    return CACHE[key]


def _summary(M, sig):
    w = max(M) - min(M) + 1
    res = [decide(M, sig, q) for q in range(2, 2 * w + 1)]
    return 'preinj@every-q=%s inj@every-q=%s preinj-q=%s inj-q=%s' % (
        all(r[0] for r in res), all(r[1] for r in res),
        [q for q, r in zip(range(2, 2 * w + 1), res) if r[0]],
        [q for q, r in zip(range(2, 2 * w + 1), res) if r[1]])


def main(path, specs):
    block, lines = None, collections.defaultdict(list)
    for line in open(path):
        if line.startswith('== '):
            block = tuple(line.split()[1:3])
        elif line.startswith('  fd3') and block and block[0] == 'Z':
            lines[block].append(line)
    for (_, spec), rows in lines.items():
        if specs and spec not in specs:
            continue
        M = [int(t) for t in spec.split(',')]
        print('== Z', spec, '(fd2-passers)')
        for row in rows:
            parts = row.split(None, 6)
            sig = {p: int(m) for p, m in ast.literal_eval(parts[6]).items()}
            print('  fd3 %s mp %s perm %s ->' % (parts[1], parts[3], parts[5]), summary(M, sig), sig)
            sys.stdout.flush()
        tab = collections.Counter()
        for sig in e_permutive(M):
            tab[summary(M, sig).split(' preinj-q')[0]] += 1
        print('  e-permutive selectors:', dict(tab))
        sys.stdout.flush()


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2:])
