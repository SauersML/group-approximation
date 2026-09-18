#!/usr/bin/env python3
"""Checks for non-affine-sigma-deletions-defeat-low-degree-collapse (p = 2).

Part A  (counterexample).  Outer game Phi: n vertices, label space F_2^k, edges e=(a,b)
        with H_e = graph of a random invertible M_e.  Identity views.  Exact triple
        sigma = M_e; perturbed triple sigma'_e = M_e o swap(0, u_e), u_e != 0.
        Exhaustively computes val(Phi as UG) (= 1 via x = 0), val(V_pert), val(V_mix),
        the oblivious completeness 1 - 2^(1-k) (pert) and 1 - 2^(-k) (mix), and checks
        the per-edge score table used in the proof: a mixed edge scores 1/2 without
        randomness only when both endpoints are labelled 0.

Part B  (deletion collapse, affine views, arbitrary sigma).  Random linear outer games with a
        planted homogeneous symmetry space S, random affine views, random bijections sigma
        (half of them sparse perturbations of the induced bijection).  Checks:
        (R)  a triple whose view kernels differ on H_e accepts at most 1/2 of H_e;
        (W)  w_r >= 2c - 1, and sum_r tau_t (1 - a_t) <= 1 - c;
        (D)  the deletion set D_t has density a_t in A_a/K;
        (T)  pointwise transfer: every labelling l of Can_del induces F_l with
             acc_V(F_l) >= w_r * val_del(l)  (equality on the roundable part);
        (S)  S preserves the value of Can and the spread bound
             avg_s val_del(l + s) >= val_Can(l) - sum_r (tau_t/w_r)(1-a_t)[A_a/K : image of S];
        (M)  by brute force, val(V) >= w_r * val(Can_del) whenever enumeration is small.
Single-threaded.  Run: nice -n 10 timeout 1200 python3 check_deletion_collapse.py [seed] [trials]
"""
import itertools, random, sys
import numpy as np

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20260917
random.seed(SEED)
np.random.seed(SEED % (2**32))
fails = 0


def fail(msg):
    global fails
    fails += 1
    print("FAIL", msg)


def mat_apply(M, v):
    return sum(((bin(r & v).count("1") & 1) << t) for t, r in enumerate(M))


def rank(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def rand_invertible(n):
    while True:
        M = [random.randrange(1 << n) for _ in range(n)]
        if rank(M) == n:
            return M


def span(gens, base=0):
    pts = {base}
    for g in gens:
        pts |= {q ^ g for q in pts}
    return sorted(pts)


# ---------------------------------------------------------------- Part A
def part_a(n, k, m):
    K = 1 << k
    edges = []
    for _ in range(m):
        a, b = random.sample(range(n), 2)
        M = rand_invertible(k)
        u = random.randrange(1, K)
        exact = np.array([mat_apply(M, x) for x in range(K)])
        swap = list(range(K))
        swap[0], swap[u] = u, 0
        pert = np.array([mat_apply(M, swap[x]) for x in range(K)])
        edges.append((a, b, exact, pert, u, M))
    labs = np.array(list(itertools.product(range(K), repeat=n)), dtype=np.int64)
    acc_ex = np.zeros(len(labs))
    acc_pe = np.zeros(len(labs))
    comp_pe = 0.0
    for a, b, exact, pert, u, M in edges:
        acc_ex += exact[labs[:, a]] == labs[:, b]
        acc_pe += pert[labs[:, a]] == labs[:, b]
        comp_pe += np.mean(pert == exact)  # honest x_a uniform, x_b = M x_a
        # score table of the mixed edge
        for xa in range(K):
            for xb in range(K):
                s = 0.5 * (int(exact[xa] == xb) + int(pert[xa] == xb))
                if xa not in (0, u):
                    if s not in (0.0, 1.0) or (s == 1.0) != (xb == exact[xa]):
                        fail("A score table off fibre")
                else:
                    if s not in (0.0, 0.5):
                        fail("A score table on {0,u}")
    comp_pe /= m
    val_phi = acc_ex.max() / m
    zero_ok = acc_ex[0] == m
    val_pe = acc_pe.max() / m
    val_mix = (0.5 * (acc_ex + acc_pe)).max() / m
    if not zero_ok or val_phi != 1.0:
        fail("A zero labelling not perfect for Phi")
    if abs(comp_pe - (1 - 2.0 / K)) > 1e-12:
        fail("A completeness %r" % comp_pe)
    if acc_pe[0] != 0:
        fail("A perturbed game accepts the zero labelling somewhere")
    print("A n=%d k=%d m=%d: val(Can)=val(Phi)=%.3f  completeness(pert)=%.4f  val(V_pert)=%.3f  "
          "completeness(mix)=%.4f  val(V_mix)=%.3f  w_ex(mix)=0.5" %
          (n, k, m, val_phi, comp_pe, val_pe, 1 - 1.0 / K, val_mix))
    return val_pe, val_mix


# ---------------------------------------------------------------- Part B
def part_b(trial):
    nz = 3
    dims = [random.choice([2, 3]) for _ in range(nz)]
    k = 2
    # planted symmetry direction
    s0 = [random.randrange(1 << d) for d in dims]
    edges = []
    for _ in range(random.randint(2, 4)):
        a, b = random.sample(range(nz), 2)
        da, db = dims[a], dims[b]
        while True:
            r = random.randint(max(da, db), da + db)
            gens = [random.randrange(1 << (da + db)) for _ in range(r)]
            if random.random() < 0.7:
                gens.append(s0[a] | (s0[b] << da))
            lin = span(gens)
            pa = {v & ((1 << da) - 1) for v in lin}
            pb = {v >> da for v in lin}
            if len(pa) == 1 << da and len(pb) == 1 << db:
                break
        off = random.randrange(1 << (da + db))
        pts = [v ^ off for v in lin]
        edges.append((a, b, set(lin), pts))
    # views: 2 per vertex
    views = []
    for z in range(nz):
        for _ in range(2):
            A = [random.randrange(1 << dims[z]) for _ in range(k)]
            c = random.randrange(1 << k)
            views.append((z, A, c))

    def rho(w, x):
        z, A, c = views[w]
        return mat_apply(A, x) ^ c

    def partition(w):
        z = views[w][0]
        ids, sig = {}, []
        for x in range(1 << dims[z]):
            y = rho(w, x)
            ids.setdefault(y, len(ids))
            sig.append(ids[y])
        return (z, tuple(sig))

    canv = {}
    for w in range(len(views)):
        canv.setdefault(partition(w), len(canv))
    vkey = [canv[partition(w)] for w in range(len(views))]
    nclass = {}
    for key, i in canv.items():
        nclass[i] = max(key[1]) + 1

    def cls(w, x):
        return partition(w)[1][x]

    def rep(w, j):  # a representative x of class j of view w
        return partition(w)[1].index(j)

    triples = []
    for ei, (a, b, lin, pts) in enumerate(edges):
        for _ in range(random.randint(2, 5)):
            w = random.choice([u for u in range(len(views)) if views[u][0] in (a, b)])
            w2 = random.choice([u for u in range(len(views)) if views[u][0] in (a, b)])
            da = dims[a]

            def coord(h, u):
                return h & ((1 << da) - 1) if views[u][0] == a else h >> da
            rel = {(rho(w, coord(h, w)), rho(w2, coord(h, w2))) for h in pts}
            f_img = {p for p, q in rel}
            g_img = {q for p, q in rel}
            bij = len(rel) == len(f_img) == len(g_img)
            if bij and random.random() < 0.6:
                beta = dict(rel)
                perm = list(range(1 << k))
                src = sorted(beta)
                dst = [beta[y] for y in src]
                rest_s = [y for y in range(1 << k) if y not in beta]
                rest_d = [y for y in range(1 << k) if y not in dst]
                random.shuffle(rest_d)
                for y, t in zip(src + rest_s, dst + rest_d):
                    perm[y] = t
                if random.random() < 0.7:
                    i, j = random.sample(range(1 << k), 2)
                    perm[i], perm[j] = perm[j], perm[i]
            else:
                perm = list(range(1 << k))
                random.shuffle(perm)
            tau = random.random()
            triples.append((ei, w, w2, perm, tau))
    tot = sum(t[4] for t in triples)
    triples = [(ei, w, w2, perm, tau / tot) for ei, w, w2, perm, tau in triples]

    c = 0.0
    w_r = 0.0
    del_mass = 0.0
    rt = []  # roundable triples with (beta on classes, D_t)
    for ei, w, w2, perm, tau in triples:
        a, b, lin, pts = edges[ei]
        da = dims[a]

        def coord(h, u):
            return h & ((1 << da) - 1) if views[u][0] == a else h >> da
        acc = np.mean([perm[rho(w, coord(h, w))] == rho(w2, coord(h, w2)) for h in pts])
        c += tau * acc
        clsrel = {(cls(w, coord(h, w)), cls(w2, coord(h, w2))) for h in pts}
        roundable = len(clsrel) == len({p for p, q in clsrel}) == len({q for p, q in clsrel})
        if not roundable:
            if acc > 0.5 + 1e-12:
                fail("R non-roundable triple accepts %r" % acc)
            continue
        beta = dict(clsrel)
        if len(beta) != nclass[vkey[w]]:
            fail("R beta not onto classes")
        D = {j for j in beta if perm[rho(w, rep(w, j))] == rho(w2, rep(w2, beta[j]))}
        if abs(len(D) / len(beta) - acc) > 1e-12:
            fail("D deletion density %r vs %r" % (len(D) / len(beta), acc))
        w_r += tau
        del_mass += tau * (1 - acc)
        rt.append((ei, w, w2, perm, tau, beta, D))
    if w_r < 2 * c - 1 - 1e-12:
        fail("W w_r=%r < 2c-1, c=%r" % (w_r, c))
    if del_mass > 1 - c + 1e-12:
        fail("W deletion mass %r > 1-c" % del_mass)
    if w_r == 0:
        return 0
    nv = len(canv)
    sizes = [nclass[i] for i in range(nv)]

    def val_can(l, deletions):
        s = 0.0
        for ei, w, w2, perm, tau, beta, D in rt:
            j = l[vkey[w]]
            if beta[j] == l[vkey[w2]] and (not deletions or j in D):
                s += tau
        return s / w_r

    def acc_F(F):
        s = 0.0
        for ei, w, w2, perm, tau in triples:
            if perm[F[w]] == F[w2]:
                s += tau
        return s

    total = 1
    for sz in sizes:
        total *= sz
    labellings = itertools.product(*[range(sz) for sz in sizes]) if total <= 5000 else \
        (tuple(random.randrange(sz) for sz in sizes) for _ in range(600))
    # symmetry space S
    S = []
    for s in itertools.product(*[range(1 << d) for d in dims]):
        if all((s[a] | (s[b] << dims[a])) in lin for a, b, lin, pts in edges):
            S.append(s)
    for l in labellings:
        F = [rho(w, rep(w, l[vkey[w]])) for w in range(len(views))]
        vd = val_can(l, True)
        if acc_F(F) < w_r * vd - 1e-12:
            fail("T transfer")
        vc = val_can(l, False)
        # shift by S
        tot_del = 0.0
        for s in S:
            l2 = list(l)
            for w in range(len(views)):
                z = views[w][0]
                l2[vkey[w]] = cls(w, rep(w, l[vkey[w]]) ^ s[z])
            if abs(val_can(l2, False) - vc) > 1e-12:
                fail("S symmetry does not preserve val(Can)")
            tot_del += val_can(l2, True)
        loss = 0.0
        for ei, w, w2, perm, tau, beta, D in rt:
            z = views[w][0]
            img = {cls(w, s[z]) for s in S}
            loss += (tau / w_r) * (1 - len(D) / len(beta)) * (len(beta) / len(img))
        if tot_del / len(S) < vc - loss - 1e-12:
            fail("S spread bound")
    # brute force val(V) vs w_r val(Can_del)
    if (1 << k) ** len(views) <= 70000 and total <= 5000:
        best_can = max(val_can(l, True) for l in itertools.product(*[range(sz) for sz in sizes]))
        labs = np.array(list(itertools.product(range(1 << k), repeat=len(views))), dtype=np.int64)
        accv = np.zeros(len(labs))
        for ei, w, w2, perm, tau in triples:
            accv += tau * (np.array(perm)[labs[:, w]] == labs[:, w2])
        if accv.max() < w_r * best_can - 1e-9:
            fail("M val(V) < w_r val(Can_del)")
        return 1
    return 0


TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 70
print("seed", SEED, flush=True)
for (n, k, m) in [(4, 3, 24), (4, 4, 30), (5, 3, 40), (5, 4, 40)]:
    part_a(n, k, m)
    sys.stdout.flush()
brute = 0
for trial in range(TRIALS):
    brute += part_b(trial)
    if (trial + 1) % 25 == 0:
        print("B progress", trial + 1, "failures so far", fails, flush=True)
print("B %d random verifiers checked (R,W,D,T,S); brute-force (M) on" % TRIALS, brute)
print("failures:", fails)
sys.exit(1 if fails else 0)
