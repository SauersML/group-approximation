#!/usr/bin/env python3
"""Exact census of rank-deficient tower coverings over Thompson's group V.

Certificate (research/rank-deficient-tower-coverings-decide-binary-cyclic-corner.md, coset form):
    delta_1 = f_1 + ... + f_r over F_2,
with f_j finitely supported and constant on every set K_j w, where K_j = x_j C x_j^-1,
C = C_3^k = <g, D(g), ..., D^(k-1)(g)>, and r < 3^k. Such a certificate makes the binary
cyclic corner full and F_2[V] not directly finite.

A bounded instance takes L = <K_1, ..., K_r>, a left-multiplication ball Y of L, one F_2 variable
per coset K_j w meeting Y, and one equation per element of the union of those cosets. It is exact:
feasible means a certificate supported there, infeasible means none. Two solvers:
    peel  : XOR peeling of single-variable equations, then an XOR basis on the core;
    dense : an XOR basis on the whole system (no peeling), the independent cross-check.

Group law: elements are prefix-code bijections {domain leaf: range leaf}; (a*b)(x) = a(b(x)).
Pure Python 3, stdlib only.
"""
import argparse, json, random, sys, time

T3 = ('0', '10', '11')  # the ternary family s_1 = s0, s_2 = s1 s0, s_3 = s1 s1


# ---------------------------------------------------------------- Thompson V
def reduce_pairs(d):
    d = dict(d)
    changed = True
    while changed:
        changed = False
        for a in list(d):
            if a not in d or not a or a[-1] != '0':
                continue
            sib = a[:-1] + '1'
            if sib not in d:
                continue
            ra, rs = d[a], d[sib]
            if ra and rs and ra[:-1] == rs[:-1] and ra[-1] == '0' and rs[-1] == '1':
                del d[a], d[sib]
                d[a[:-1]] = ra[:-1]
                changed = True
    return d


def key(d):
    return tuple(sorted(d.items()))


def find_prefix(a, word):
    for i in range(len(word) + 1):
        if word[:i] in a:
            return word[:i]
    return None


def mul(a, b):
    """a*b: apply b first, then a."""
    res = {}
    for dom, rng in b.items():
        p = find_prefix(a, rng)
        if p is not None:
            res[dom] = a[p] + rng[len(p):]
        else:
            for leaf, img in a.items():
                if leaf.startswith(rng):
                    res[dom + leaf[len(rng):]] = img
    return reduce_pairs(res)


def inv(a):
    return {v: k for k, v in a.items()}


ONE = {'': ''}
G = {'0': '10', '10': '11', '11': '0'}


def D(h):
    return reduce_pairs({c + d: c + r for c in T3 for d, r in h.items()})


def closure(gens, cap=100000):
    seen = {key(ONE): ONE}
    frontier = [ONE]
    while frontier:
        nxt = []
        for w in frontier:
            for s in gens:
                u = mul(s, w)
                ku = key(u)
                if ku not in seen:
                    seen[ku] = u
                    nxt.append(u)
        frontier = nxt
        if len(seen) > cap:
            raise RuntimeError('closure too large')
    return list(seen.values())


def tower_group(k):
    gens, h = [], G
    for _ in range(k):
        gens.append(h)
        h = D(h)
    return closure(gens)


def conjugate(x, K):
    xi = inv(x)
    return [mul(mul(x, h), xi) for h in K]


def random_code(n, rng):
    leaves = ['']
    for _ in range(n - 1):
        w = leaves.pop(rng.randrange(len(leaves)))
        leaves += [w + '0', w + '1']
    return leaves


def random_element(n, rng):
    dom, ran = random_code(n, rng), random_code(n, rng)
    rng.shuffle(ran)
    return reduce_pairs(dict(zip(dom, ran)))


def cylinder_words(k):
    words = ['']
    for _ in range(k):
        words = [w + c for w in words for c in T3]
    return words


def cylinder_permutation(k, perm):
    words = cylinder_words(k)
    return reduce_pairs({words[i]: words[perm[i]] for i in range(len(words))})


# ---------------------------------------------------------------- instances
def build_instance(subgroups, budget):
    gens = [h for K in subgroups for h in K if key(h) != key(ONE)]
    ball = {key(ONE): ONE}
    frontier = [ONE]
    while frontier and len(ball) < budget:
        nxt = []
        for w in frontier:
            for s in gens:
                u = mul(s, w)
                ku = key(u)
                if ku not in ball:
                    ball[ku] = u
                    nxt.append(u)
                    if len(ball) >= budget:
                        break
            if len(ball) >= budget:
                break
        frontier = nxt
    var_id, var_members, elem_vars = {}, [], {}
    for w in ball.values():
        for j, K in enumerate(subgroups):
            members = [key(mul(h, w)) for h in K]
            ck = (j, min(members))
            if ck in var_id:
                continue
            v = len(var_members)
            var_id[ck] = v
            var_members.append(members)
            for m in members:
                elem_vars.setdefault(m, []).append(v)
    return ball, var_members, elem_vars


def xor_basis_consistent(rows, rhs_pos):
    """rows: ints with variable bits below rhs_pos and the right-hand side at rhs_pos."""
    basis, rhs_low = {}, 1 << rhs_pos
    for r in rows:
        while r:
            low = r & -r
            if low == rhs_low:
                return False
            if low in basis:
                r ^= basis[low]
            else:
                basis[low] = r
                break
    return True


def solve_peel(var_members, elem_vars):
    one = key(ONE)
    rows = {u: set(vs) for u, vs in elem_vars.items()}
    rhs = {u: (1 if u == one else 0) for u in rows}
    var_rows = [[] for _ in var_members]
    for u, vs in rows.items():
        for v in vs:
            var_rows[v].append(u)
    queue = [u for u, vs in rows.items() if len(vs) == 1]
    while queue:
        u = queue.pop()
        if len(rows[u]) != 1:
            continue
        v = next(iter(rows[u]))
        val = rhs[u]
        for u2 in var_rows[v]:
            if v in rows[u2]:
                rows[u2].discard(v)
                if val:
                    rhs[u2] ^= 1
                if len(rows[u2]) == 1:
                    queue.append(u2)
                elif not rows[u2] and rhs[u2]:
                    return False, 0
    core = sorted({v for vs in rows.values() for v in vs})
    idx = {v: i for i, v in enumerate(core)}
    n = len(core)
    live = ((sum(1 << idx[v] for v in vs) | (rhs[u] << n)) for u, vs in rows.items() if vs)
    return xor_basis_consistent(live, n), n


def solve_dense(var_members, elem_vars):
    one = key(ONE)
    n = len(var_members)
    rows = ((sum(1 << v for v in vs) | ((1 << n) if u == one else 0)) for u, vs in elem_vars.items())
    return xor_basis_consistent(rows, n)


def run_instance(name, subgroups, budget, rank_bound, dense_limit):
    t0 = time.time()
    ball, var_members, elem_vars = build_instance(subgroups, budget)
    ok_peel, core = solve_peel(var_members, elem_vars)
    out = {
        'name': name, 'r': len(subgroups), 'rank_bound': rank_bound, 'ball': len(ball),
        'variables': len(var_members), 'equations': len(elem_vars), 'core_variables': core,
        'feasible_peel': ok_peel,
    }
    if len(var_members) <= dense_limit:
        out['feasible_dense'] = solve_dense(var_members, elem_vars)
    out['seconds'] = round(time.time() - t0, 2)
    return out


# ---------------------------------------------------------------- driver
def self_tests(rng):
    assert key(mul(G, mul(G, G))) == key(ONE) and key(G) != key(ONE)
    for _ in range(200):
        a, b, c = (random_element(rng.randint(1, 6), rng) for _ in range(3))
        assert key(mul(a, mul(b, c))) == key(mul(mul(a, b), c))
        assert key(mul(a, inv(a))) == key(ONE)
        assert key(D(mul(a, b))) == key(mul(D(a), D(b)))
        assert key(mul(D(a), G)) == key(mul(G, D(a)))
    sizes = [len(tower_group(k)) for k in (1, 2, 3)]
    assert sizes == [3, 9, 27], sizes
    return {'self_tests': 'PASS', 'tower_sizes': sizes}


def controls(args, rng, emit):
    emit(self_tests(rng))
    C1, C2 = tower_group(1), tower_group(2)
    dg = D(G)
    four = [closure([h]) for h in (G, dg, mul(G, dg), mul(G, mul(dg, dg)))]
    res = run_instance('positive-four-order-three-subgroups-of-C3sq', four, args.budget, 3, args.dense)
    res['expected'] = True
    emit(res)
    fails = int(res['feasible_peel'] is not True or res.get('feasible_dense', True) is not True)
    for s in range(args.samples):
        x = random_element(rng.randint(3, args.leaves), rng)
        K2 = conjugate(x, C1)
        if {key(h) for h in K2} == {key(h) for h in C1}:
            continue
        res = run_instance('lemma-k1-r2-sample-%d' % s, [C1, K2], args.budget, 3, args.dense)
        res['expected'] = False
        fails += int(res['feasible_peel'] is not False or res.get('feasible_dense', False) is not False)
        emit(res)
    for s in range(max(1, args.samples // 2)):
        subs = [C2]
        for _ in range(7):
            perm = list(range(9))
            rng.shuffle(perm)
            subs.append(conjugate(cylinder_permutation(2, perm), C2))
        res = run_instance('finite-k2-r8-cylinder-sample-%d' % s, subs, args.budget, 9, args.dense)
        res['expected'] = False
        fails += int(res['feasible_peel'] is not False or res.get('feasible_dense', False) is not False)
        emit(res)
    emit({'controls_failed': fails})
    return fails


def census(args, rng, emit):
    C2 = tower_group(2)
    base = {key(h) for h in C2}
    for r in [int(t) for t in args.rs.split(',')]:
        for s in range(args.samples):
            subs, xs = [C2], []
            while len(subs) < r:
                x = random_element(rng.randint(2, args.leaves), rng)
                K = conjugate(x, C2)
                if {key(h) for h in K} == base:
                    continue
                subs.append(K)
                xs.append(key(x))
            res = run_instance('census-k2-r%d-sample-%d' % (r, s), subs, args.budget, 9, args.dense)
            res['conjugators'] = xs
            emit(res)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['controls', 'census'], required=True)
    ap.add_argument('--budget', type=int, default=2000)
    ap.add_argument('--samples', type=int, default=6)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--leaves', type=int, default=5)
    ap.add_argument('--rs', default='2,3,4,8')
    ap.add_argument('--dense', type=int, default=4000)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    with open(args.out, 'w') as fh:
        def emit(obj):
            fh.write(json.dumps(obj) + '\n')
            fh.flush()
        emit({'args': vars(args)})
        if args.mode == 'controls':
            sys.exit(1 if controls(args, rng, emit) else 0)
        census(args, rng, emit)
        emit({'done': True})


if __name__ == '__main__':
    main()
