#!/usr/bin/env python3
"""Checks for thompson-gap-witnesses-need-nonamenable-image.

Part 1 (exact).  V: abelianization of G0 = S4 *_<a> S3 is Z/2 via the sign eta
(a, c -> -1, b -> +1).  Compute eta(r5..r8) from the Bleak--Quick words.
Part 2 (exact).  T: abelianization of Z/4 * Z/3 is Z/4 x Z/3.  For every nontrivial
character chi, compute max over the three Lochak--Schneps relators of |chi(r) - 1|,
and report the minimum over chi.
Part 3 (sanity, numerical).  Random monomial (hence finite-image, virtually abelian)
representations of G0: sums of inductions of characters of random subgroups of S4 and
S3, glued along a by a random monomial matrix.  Report min D over nontrivial samples;
the theorem predicts D >= 1/2 for every one of them.

Word convention: letters read left to right, x^-1 is inverse, (w)^k is a power.
Only exponent sums matter for Parts 1 and 2; Part 3 multiplies matrices left to right
(the value of ||rho(r) - 1|| is the same for the reversed convention up to
replacing rho by its transpose-inverse, which is again a monomial representation).
"""
import itertools, json, math, os, random, re, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REL_V = os.path.join(HERE, "..", "thompson-v-models", "rel_V.txt")


def expand(word):
    """Expand '(...)^k' and 'x^-1' into a list of (letter, +-1)."""
    out, i = [], 0
    while i < len(word):
        ch = word[i]
        if ch == "(":
            depth, j = 1, i + 1
            while depth:
                depth += {"(": 1, ")": -1}.get(word[j], 0)
                j += 1
            inner = expand(word[i + 1 : j - 1])
            m = re.match(r"\^(-?\d+)", word[j:])
            k = int(m.group(1)) if m else 1
            if m:
                j += len(m.group(0))
            if k < 0:
                inner = [(x, -e) for (x, e) in reversed(inner)]
                k = -k
            out += inner * k
            i = j
        else:
            m = re.match(r"\^(-?\d+)", word[i + 1 :])
            if m:
                k = int(m.group(1))
                out += [(ch, 1 if k > 0 else -1)] * abs(k)
                i += 1 + len(m.group(0))
            else:
                out.append((ch, 1))
                i += 1
    return out


def part1():
    words = [w.strip() for w in open(REL_V) if w.strip()]
    res = []
    for idx, w in enumerate(words):
        ex = expand(w)
        par = sum(1 for (x, e) in ex if x in "ac") % 2
        res.append({"relator": f"r{idx+5}", "length": len(ex),
                    "ac_letters_mod2": par, "eta": -1 if par else 1})
    return res


def part2():
    # a = alpha (order 4), b = beta (order 3); exponent sums
    # r_1, r_2 are commutators, so their exponent sums vanish; r_P = (beta alpha)^5.
    # exponent sums of the three relators in Z/4 x Z/3
    sums = {"r_1": (0, 0), "r_2": (0, 0), "r_P": (5 % 4, 5 % 3)}
    best = None
    table = []
    for j in range(4):
        for k in range(3):
            if (j, k) == (0, 0):
                continue
            ds = []
            for name, (ea, eb) in sums.items():
                z = np.exp(2j * np.pi * (j * ea / 4 + k * eb / 3))
                ds.append(abs(z - 1))
            D = max(ds)
            table.append({"chi_a": f"i^{j}", "chi_b": f"omega^{k}", "D": D})
            best = D if best is None else min(best, D)
    return {"min_D_over_nontrivial_characters": best,
            "two_sin_pi_over_12": 2 * math.sin(math.pi / 12), "table": table}


# ---------- Part 3: monomial representations ----------

def pmul(p, q):  # apply p then q (right action)
    return tuple(q[p[i]] for i in range(len(p)))


def closure(gens, n):
    e = tuple(range(n))
    seen, frontier = {e}, [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = pmul(x, g)
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return seen


def character_on(Hgens, n, K):
    """Random hom chi: <Hgens> -> mu_K, or None if the random values are inconsistent."""
    e = tuple(range(n))
    vals = [random.randrange(K) for _ in Hgens]
    chi, frontier = {e: 0}, [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g, v in zip(Hgens, vals):
                y = pmul(x, g)
                t = (chi[x] + v) % K
                if y in chi:
                    if chi[y] != t:
                        return None
                else:
                    chi[y] = t
                    nxt.append(y)
        frontier = nxt
    return chi


def induced(Gelems, Hgens, n, gens, K, tries=50):
    for _ in range(tries):
        chi = character_on(Hgens, n, K)
        if chi is not None:
            break
    else:
        return None
    H = set(chi)
    # left cosets gH: choose representatives
    reps, covered = [], set()
    for g in sorted(Gelems):
        if g in covered:
            continue
        reps.append(g)
        for h in H:
            covered.add(pmul(h, g))  # right-action convention: coset H g
    m = len(reps)
    idx = {}
    for i, g in enumerate(reps):
        for h in H:
            idx[pmul(h, g)] = (i, h)
    mats = []
    for s in gens:
        M = np.zeros((m, m), complex)
        for i, g in enumerate(reps):
            j, h = idx[pmul(g, s)]  # g s = h * reps[j]
            M[i, j] = np.exp(2j * np.pi * chi[h] / K)
        mats.append(M)
    return mats


def random_rep(Gelems, n, gens, K, blocks):
    Ms = [[] for _ in gens]
    Gl = sorted(Gelems)
    for _ in range(blocks):
        Hgens = [random.choice(Gl) for _ in range(random.randint(0, 2))]
        r = induced(Gelems, Hgens, n, gens, K)
        if r is None:
            continue
        for t, M in enumerate(r):
            Ms[t].append(M)
    if not Ms[0]:
        return None
    from scipy.linalg import block_diag
    return [block_diag(*L) for L in Ms]


def involution_normal_form(M):
    """Monomial involution M -> (P, counts) with P M P^-1 canonical:
    diag(+1 block, -1 block, swap blocks)."""
    n = M.shape[0]
    perm = [int(np.argmax(abs(M[i]))) for i in range(n)]
    plus, minus, pairs = [], [], []
    done = set()
    for i in range(n):
        if i in done:
            continue
        j = perm[i]
        if j == i:
            (plus if M[i, i].real > 0 else minus).append(i)
            done.add(i)
        else:
            pairs.append((i, j))
            done |= {i, j}
    order = plus + minus + [x for p in pairs for x in p]
    P = np.zeros((n, n), complex)
    for new, old in enumerate(order):
        P[new, old] = 1
    # rescale second coordinate of each pair so the block becomes [[0,1],[1,0]]
    D = np.eye(n, dtype=complex)
    base = len(plus) + len(minus)
    for k, (i, j) in enumerate(pairs):
        u = M[i, j]  # M e_j component: row i col j
        D[base + 2 * k + 1, base + 2 * k + 1] = u
    Q = D @ P
    C = Q @ M @ np.linalg.inv(Q)
    return Q, (len(plus), len(minus), len(pairs)), C


def random_centralizer(counts, K):
    p, m, q = counts
    n = p + m + 2 * q
    C = np.zeros((n, n), complex)
    ph = lambda: np.exp(2j * np.pi * random.randrange(K) / K)
    for blk in (list(range(p)), list(range(p, p + m))):
        sh = blk[:]
        random.shuffle(sh)
        for s, t in zip(blk, sh):
            C[s, t] = ph()
    base = p + m
    order = list(range(q))
    random.shuffle(order)
    for k, l in enumerate(order):
        z = ph()
        if random.random() < 0.5:
            C[base + 2 * k, base + 2 * l] = z
            C[base + 2 * k + 1, base + 2 * l + 1] = z
        else:
            C[base + 2 * k, base + 2 * l + 1] = z
            C[base + 2 * k + 1, base + 2 * l] = z
    return C


def word_matrix(ex, gens):
    n = next(iter(gens.values())).shape[0]
    M = np.eye(n, dtype=complex)
    for x, e in ex:
        g = gens[x]
        M = M @ (g if e > 0 else g.conj().T)
    return M


def part3(samples=40000, seed=1):
    random.seed(seed)
    S4 = closure([(1, 0, 2, 3), (0, 2, 3, 1)], 4)  # a = (0 1), b = (1 2 3)
    S3 = closure([(1, 0, 2), (2, 1, 0)], 3)          # a = (0 1), c = (0 2)
    a4, b4 = (1, 0, 2, 3), (0, 2, 3, 1)
    a3, c3 = (1, 0, 2), (2, 1, 0)
    # sanity on the permutation models of the finite pieces
    assert len(S4) == 24 and len(S3) == 6
    words = [expand(w.strip()) for w in open(REL_V) if w.strip()]
    K = 12
    best, tried, kept = None, 0, 0
    for _ in range(samples):
        tried += 1
        r4 = random_rep(S4, 4, [a4, b4], K, random.randint(1, 4))
        r3 = random_rep(S3, 3, [a3, c3], K, random.randint(1, 5))
        if r4 is None or r3 is None:
            continue
        (A4, B4), (A3, C3) = r4, r3
        if A4.shape != A3.shape:
            continue
        Q4, c4, _ = involution_normal_form(A4)
        Q3, c3n, _ = involution_normal_form(A3)
        if c4 != c3n:
            continue
        W = np.linalg.inv(Q4) @ random_centralizer(c4, K) @ Q3
        a, b, c = A4, B4, W @ C3 @ np.linalg.inv(W)
        if np.linalg.norm(W @ A3 @ np.linalg.inv(W) - a) > 1e-9:
            continue
        # relations of G0
        I = np.eye(a.shape[0])
        rel = [a @ a, np.linalg.matrix_power(b, 3), np.linalg.matrix_power(a @ b, 4),
               c @ c, np.linalg.matrix_power(a @ c, 3)]
        assert all(np.linalg.norm(R - I) < 1e-8 for R in rel)
        if np.linalg.norm(a - I) < 1e-9:
            continue  # trivial representation
        kept += 1
        g = {"a": a, "b": b, "c": c}
        D = max(np.linalg.norm(word_matrix(ex, g) - I, 2) for ex in words)
        best = D if best is None else min(best, D)
    return {"samples": tried, "nontrivial_glued": kept, "min_D": best,
            "predicted_lower_bound": 0.5}


if __name__ == "__main__":
    out = {"part1_V_sign_character": part1(), "part2_T_characters": part2()}
    out["part3_monomial_V"] = part3()
    print(json.dumps({k: (v if k != "part2_T_characters" else
                          {kk: vv for kk, vv in v.items() if kk != "table"})
                      for k, v in out.items()}, indent=1))
    with open(os.path.join(HERE, "out_abelian_and_monomial_check.json"), "w") as f:
        json.dump(out, f, indent=1)
