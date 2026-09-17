#!/usr/bin/env python3
"""Randomized exhaustive checks for the linear-view collapse theorem (p = 2).

Checks, on random small instances:
 (L1) arbitrary bijection sigma, affine views rho, rho' on an affine space H:
      density{x : sigma(rho x) = rho' x} <= 1/[ker : ker cap ker'] (both ways),
      so distinct kernels give density <= 1/2.
 (L2) affine sigma: density in {0} U {2^-j}; density > 1/2 implies density 1.
 (NF) linear-view verifier G over an outer linear game Phi (2-to-2 or projection):
      weight of exact edges >= 2c - 1, beta_e is determined by (H_e, K, K'),
      exact 2-to-2 edges kill both branch directions, and by brute force
      val(G) >= w_ex * val(Can).
Single-threaded; run with: nice -n 10 timeout 1200 python3 check_collapse.py
"""
import itertools, random, sys

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 12345)

def vec(i, n):  # int -> tuple bits
    return tuple((i >> t) & 1 for t in range(n))

def ival(v):
    return sum(b << t for t, b in enumerate(v))

def mat_apply(M, v):  # M: list of rows (ints bitmask), v int
    return sum(((bin(r & v).count("1") & 1) << t) for t, r in enumerate(M))

def rand_mat(rows, cols):
    return [random.randrange(1 << cols) for _ in range(rows)]

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
        M = rand_mat(n, n)
        if rank(M) == n:
            return M

def affine_space(gens, base):
    pts = {base}
    for g in gens:
        pts |= {q ^ g for q in pts}
    return sorted(pts)

def kernel(view, pts):
    # kernel of the linear part of an affine map restricted to affine space pts
    x0 = pts[0]
    return frozenset(x ^ x0 for x in pts if view(x) == view(x0))

fails = 0

# ---- (L1)/(L2)
for trial in range(3000):
    n, k = 4, random.choice([1, 2, 3])
    dimH = random.randrange(1, n + 1)
    H = affine_space([random.randrange(1 << n) for _ in range(dimH)], random.randrange(1 << n))
    A, a = rand_mat(k, n), random.randrange(1 << k)
    B, b = rand_mat(k, n), random.randrange(1 << k)
    rho = lambda x: mat_apply(A, x) ^ a
    rhop = lambda x: mat_apply(B, x) ^ b
    K, Kp = kernel(rho, H), kernel(rhop, H)
    idx1 = len(K) // len(K & Kp)
    idx2 = len(Kp) // len(K & Kp)
    perm = list(range(1 << k)); random.shuffle(perm)
    dens = sum(perm[rho(x)] == rhop(x) for x in H) / len(H)
    if dens > 1 / idx1 + 1e-12 or dens > 1 / idx2 + 1e-12:
        fails += 1; print("L1 FAIL", dens, idx1, idx2)
    S = rand_invertible(k); s = random.randrange(1 << k)
    dens2 = sum((mat_apply(S, rho(x)) ^ s) == rhop(x) for x in H) / len(H)
    if dens2 > 0.5 and dens2 < 1:
        fails += 1; print("L2 FAIL", dens2)
    if dens2 not in [0] + [2.0 ** -j for j in range(0, n + 1)]:
        fails += 1; print("L2 value FAIL", dens2)
print("L1/L2 done, fails =", fails)

# ---- (NF) small composed instances
def brute_value(nverts, alph, edges):
    # edges: list of (w, w', perm dict/list, weight)
    best = 0.0
    for lab in itertools.product(range(alph), repeat=nverts):
        v = sum(wt for (w, wp, pm, wt) in edges if pm[lab[w]] == lab[wp])
        if v > best:
            best = v
    return best

l = 2  # outer labels F_2^2, output alphabet F_2^2 (views into F_2^k, k<=2 embedded)
ninst = 0
stats = {"exact_cross":0,"mid_density":0,"inst_wex_pos":0,"tight":0}
for trial in range(400):
    Z = 3
    kind = random.choice(["2to2", "proj"])
    outer = []
    for (za, zb) in [(0, 1), (1, 2), (0, 2)]:
        T, Tp = rand_invertible(l), rand_invertible(l)
        bb = random.randrange(1 << l)
        c = random.randrange(1, 1 << l) if kind == "2to2" else 0
        H = [(xa, xb) for xa in range(1 << l) for xb in range(1 << l)
             if (mat_apply(T, xa) ^ mat_apply(Tp, xb) ^ bb) in (0, c)]
        outer.append((za, zb, H, T, Tp, c))
    # output vertices: 2 per outer vertex, affine views F_2^2 -> F_2^2 (maybe non-injective)
    W = []
    for z in range(Z):
        for _ in range(2):
            M = rand_mat(l, l) if random.random() < 0.5 else rand_invertible(l)
            W.append((z, M, random.randrange(1 << l)))
    view = lambda w, x: mat_apply(W[w][1], x) ^ W[w][2]
    edges = []
    cw = 0.0
    for (za, zb, H, T, Tp, c) in outer:
        cand = [w for w in range(len(W)) if W[w][0] in (za, zb)]
        for _ in range(3):
            w, wp = random.sample(cand, 2)
            # sometimes force an exact edge: sigma = transport when possible
            if random.random() < 0.5:
                S = rand_invertible(l); s = random.randrange(1 << l)
                perm = [mat_apply(S, y) ^ s for y in range(1 << l)]
            else:
                perm = list(range(1 << l)); random.shuffle(perm)
                # try to fit transport
                mp = {}
                ok = True
                for (xa, xb) in H:
                    xw = xa if W[w][0] == za else xb
                    xwp = xa if W[wp][0] == za else xb
                    y, yp = view(w, xw), view(wp, xwp)
                    if mp.get(y, yp) != yp or yp in [v for kk, v in mp.items() if kk != y]:
                        ok = False; break
                    mp[y] = yp
                if not ok:
                    continue
                rest_src = [y for y in range(1 << l) if y not in mp]
                rest_dst = [y for y in range(1 << l) if y not in mp.values()]
                random.shuffle(rest_dst)
                perm = [mp[y] if y in mp else None for y in range(1 << l)]
                for y, d in zip(rest_src, rest_dst):
                    perm[y] = d
            acc = []
            for (xa, xb) in H:
                xw = xa if W[w][0] == za else xb
                xwp = xa if W[wp][0] == za else xb
                acc.append(perm[view(w, xw)] == view(wp, xwp))
            dens = sum(acc) / len(acc)
            edges.append([w, wp, perm, 1.0, dens, (za, zb, H, T, Tp, c)])
    if not edges:
        continue
    tot = len(edges)
    for e in edges:
        e[3] = 1.0 / tot
    c_val = sum(e[3] * e[4] for e in edges)
    exact = [e for e in edges if e[4] == 1.0]
    w_ex = sum(e[3] for e in exact)
    stats["inst_wex_pos"] += w_ex > 0
    stats["exact_cross"] += sum(W[e[0]][0] != W[e[1]][0] for e in exact)
    stats["mid_density"] += sum(0.5 < e[4] < 1 for e in edges)
    if w_ex < 2 * c_val - 1 - 1e-12:
        fails += 1; print("weight FAIL", w_ex, c_val)
    for e in edges:
        if 0.5 < e[4] < 1.0:
            # allowed only for non-affine sigma; check equal kernels on H (Lemma 1)
            w, wp, perm, _, dens, (za, zb, H, T, Tp, c) = e
            fw = lambda h: view(w, h[0] if W[w][0] == za else h[1])
            fwp = lambda h: view(wp, h[0] if W[wp][0] == za else h[1])
            Hs = sorted(H)
            k1 = {tuple(q ^ p for q, p in zip(h, Hs[0])) for h in Hs if fw(h) == fw(Hs[0])}
            k2 = {tuple(q ^ p for q, p in zip(h, Hs[0])) for h in Hs if fwp(h) == fwp(Hs[0])}
            if k1 != k2:
                fails += 1; print("L1 kernel FAIL")
    # Can: vertices (z, kernel K of view on A_z = F_2^l), label = coset (canonical min rep)
    canv = {}
    def canid(w):
        z, M, off = W[w]
        K = frozenset(x for x in range(1 << l) if mat_apply(M, x) == 0)
        return canv.setdefault((z, K), len(canv))
    def coset(w, x):
        z, M, off = W[w]
        K = [y for y in range(1 << l) if mat_apply(M, y) == 0]
        return min(x ^ y for y in K)
    can_edges = []
    for e in exact:
        w, wp, perm, wt, dens, (za, zb, H, T, Tp, c) = e
        if kind == "2to2" and W[w][0] != W[wp][0]:
            # exact cross edge must kill branch directions
            Tinv_c = [x for x in range(1 << l) if mat_apply(T, x) == c][0]
            Tpinv_c = [x for x in range(1 << l) if mat_apply(Tp, x) == c][0]
            wa = w if W[w][0] == za else wp
            wb = wp if wa == w else w
            if mat_apply(W[wa][1], Tinv_c) != 0 or mat_apply(W[wb][1], Tpinv_c) != 0:
                fails += 1; print("branch FAIL")
        beta = {}
        for (xa, xb) in H:
            xw = xa if W[w][0] == za else xb
            xwp = xa if W[wp][0] == za else xb
            src, dst = coset(w, xw), coset(wp, xwp)
            if beta.get(src, dst) != dst:
                fails += 1; print("beta not a function FAIL")
            beta[src] = dst
        if len(set(beta.values())) != len(beta):
            fails += 1; print("beta not injective FAIL")
        can_edges.append((canid(w), canid(wp), beta, wt))
    # brute force val(G) over labels in F_2^2 (alphabet = 4)
    gedges = [(e[0], e[1], e[2], e[3]) for e in edges]
    vG = brute_value(len(W), 1 << l, gedges)
    # brute force val(Can): labels = coset reps; enumerate per vertex its cosets
    keys = sorted(canv, key=canv.get)
    reps = []
    for (z, K) in keys:
        reps.append(sorted({min(x ^ y for y in K) for x in range(1 << l)}))
    bestC = 0.0
    if can_edges:
        for lab in itertools.product(*reps):
            v = 0.0
            for (i, j, beta, wt) in can_edges:
                if i == j and beta.get(lab[i]) == lab[j]:
                    v += wt
                elif i != j and beta.get(lab[i]) == lab[j]:
                    v += wt
            bestC = max(bestC, v)
        valCan = bestC / w_ex
        stats["tight"] += abs(vG - w_ex * valCan) < 1e-12
        if vG < w_ex * valCan - 1e-12:
            fails += 1; print("NF FAIL", vG, w_ex, valCan)
    ninst += 1
print("NF instances checked:", ninst, "total fails =", fails, stats)
sys.exit(1 if fails else 0)
