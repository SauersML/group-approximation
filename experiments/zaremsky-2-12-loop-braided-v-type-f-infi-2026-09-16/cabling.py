#!/usr/bin/env python3
"""Cabled McCool generators in the Witzel-Zaremsky loop braid cloning system.

Conventions (as in research/artifacts/zp-loop-braid-cloning-properly-graded-2026-09-13.md):
  * words in F_n: tuples of nonzero ints, i = x_i, -i = x_i^{-1};
  * an automorphism is a dict i -> word (the image of x_i); composition f o g;
  * WZ generators: ('b', i, e) = beta_i^e (e = +-1), ('s', i) = sigma_i;
  * WZ products are right actions, L(gh) = L(g) o L(h), with left forms
    L(beta_i) = a_i : x_i -> x_i x_{i+1} x_i^{-1}, x_{i+1} -> x_i,
    L(sigma_i) = s_i : swap x_i, x_{i+1};
  * rho(beta_i) = rho(sigma_i) = (i i+1);
  * cloning (WZ (10.1)-(10.2)) and (FCS1) (gh)k_k = (g)k_{rho(h)k} (h)k_k.
Checks:
  (1) Lemma A: L((g)k_k) o d_k = d_{rho(g)k} o L(g) for random words;
  (2) well-definedness of cloning on elements (words with the same left form have clones with the
      same left form), exhaustively over short words;
  (3) the McCool relators hold for the left-form alpha_ij : x_i -> x_j x_i x_j^{-1};
  (4) the cabled McCool generators (alpha'_pq)k_k are, for every k:
        p,q != k : A_{p^,q^}             (x^ = x if x < k, x+1 if x > k)
        q = k    : A_{p^,k+1} o A_{p^,k}  (x_{p^} conjugated by the cable x_k x_{k+1})
        p = k    : A_{k,q^} o A_{k+1,q^}  (the cable conjugated by x_{q^}, no twist)
      where alpha'_pq is computed from a word that crosses the cable strand.
"""
import itertools
import random
import sys


def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def inv(w):
    return tuple(-a for a in reversed(w))


def apply(f, w):
    """Apply automorphism f (dict on generators) to word w."""
    out = []
    for a in w:
        img = f.get(abs(a), (abs(a),))
        out.extend(img if a > 0 else inv(img))
    return red(out)


def compose(f, g, n):
    """(f o g)(x_i) = f(g(x_i))."""
    return {i: apply(f, g.get(i, (i,))) for i in range(1, n + 1)}


def ident(n):
    return {i: (i,) for i in range(1, n + 1)}


def canon(f, n):
    return tuple(red(f.get(i, (i,))) for i in range(1, n + 1))


def left_gen(g, n):
    f = ident(n)
    if g[0] == 's':
        i = g[1]
        f[i], f[i + 1] = (i + 1,), (i,)
        return f
    _, i, e = g
    if e == 1:  # a_i
        f[i] = (i, i + 1, -i)
        f[i + 1] = (i,)
    else:  # a_i^{-1}
        f[i] = (i + 1,)
        f[i + 1] = (-(i + 1), i, i + 1)
    return f


def left(word, n):
    f = ident(n)
    for g in word:
        f = compose(f, left_gen(g, n), n)
    return f


def rho_gen(g, k):
    i = g[1]
    return i + 1 if k == i else (i if k == i + 1 else k)


def rho(word, k):
    for g in reversed(word):
        k = rho_gen(g, k)
    return k


def clone_gen(g, k):
    i = g[1]
    if g[0] == 's':
        mk = lambda j: ('s', j)
    else:
        e = g[2]
        mk = lambda j: ('b', j, e)
    if k < i:
        return [mk(i + 1)]
    if k == i:
        return [mk(i), mk(i + 1)]
    if k == i + 1:
        return [mk(i + 1), mk(i)]
    return [mk(i)]


def clone(word, k):
    """(g_1 ... g_r)k_k via (FCS1): the index seen by g_j is rho(g_{j+1} ... g_r)k."""
    pieces = []
    idx = k
    for g in reversed(word):
        pieces.append(clone_gen(g, idx))
        idx = rho_gen(g, idx)
    out = []
    for p in reversed(pieces):
        out.extend(p)
    return out


def delta(k, n):
    """Merge map d_k : F_n -> F_{n+1}."""
    f = {}
    for i in range(1, n + 1):
        f[i] = (i,) if i < k else ((k, k + 1) if i == k else (i + 1,))
    return f


def inv_word(word):
    out = []
    for g in reversed(word):
        out.append(g if g[0] == 's' else ('b', g[1], -g[2]))
    return out


def alpha_auto(i, j, n):
    f = ident(n)
    f[i] = (j, i, -j)
    return f


def perm_word(target, n):
    """A sigma-word u with L(u)(x_m) = x_{pi(m)}, where pi is given as a dict on {1..n}.
    Built by bubble sort and verified."""
    word = []
    goal = canon({m: (target[m],) for m in range(1, n + 1)}, n)
    perm = {m: m for m in range(1, n + 1)}  # current L(word)(x_m) = x_{perm[m]}
    for pos in range(1, n + 1):
        # we want perm[pos] = target[pos]; find m >= pos with perm[m] = target[pos]
        m = next(mm for mm in range(pos, n + 1) if perm[mm] == target[pos])
        while m > pos:
            word.append(('s', m - 1))  # right multiply by s_{m-1}: swaps images of x_{m-1}, x_m
            perm[m - 1], perm[m] = perm[m], perm[m - 1]
            m -= 1
    assert canon(left(word, n), n) == goal, "perm_word failed"
    return word


def alpha_word(i, j, n):
    """A WZ word for alpha_ij (left form A_ij : x_i -> x_j x_i x_j^{-1}), from sigma_1 beta_1 = alpha_12,
    conjugated by a permutation word sending 1 -> i, 2 -> j."""
    rest = [m for m in range(1, n + 1) if m not in (i, j)]
    target = {1: i, 2: j}
    for pos, val in zip(range(3, n + 1), rest):
        target[pos] = val
    u = perm_word(target, n)
    w = u + [('s', 1), ('b', 1, 1)] + inv_word(u)
    assert canon(left(w, n), n) == canon(alpha_auto(i, j, n), n), (i, j, n)
    return w


def random_word(n, length, rng):
    gens = [('s', i) for i in range(1, n)] + [('b', i, e) for i in range(1, n) for e in (1, -1)]
    return [rng.choice(gens) for _ in range(length)]


def check_lemma_a(rng, trials=400):
    for _ in range(trials):
        n = rng.randint(2, 6)
        w = random_word(n, rng.randint(0, 12), rng)
        k = rng.randint(1, n)
        lhs = compose(left(clone(w, k), n + 1), delta(k, n), n + 1)
        j = rho(w, k)
        rhs = compose(delta(j, n), left(w, n), n + 1)
        # compose(delta, ...) evaluates delta on words over F_n; both are maps F_n -> F_{n+1}
        lhs_c = tuple(red(lhs[i]) for i in range(1, n + 1))
        rhs_c = tuple(apply(delta(j, n), left(w, n)[i]) for i in range(1, n + 1))
        if lhs_c != rhs_c:
            return False, (n, w, k)
    return True, None


def check_well_defined(n, maxlen):
    gens = [('s', i) for i in range(1, n)] + [('b', i, e) for i in range(1, n) for e in (1, -1)]
    table = {}
    count = 0
    for length in range(maxlen + 1):
        for w in itertools.product(gens, repeat=length):
            w = list(w)
            key = canon(left(w, n), n)
            val = tuple(canon(left(clone(w, k), n + 1), n + 1) for k in range(1, n + 1))
            if key in table:
                count += 1
                if table[key] != val:
                    return False, w, count
            else:
                table[key] = val
    return True, len(table), count


def comm(f, g, n, finv, ginv):
    return compose(compose(f, g, n), compose(finv, ginv, n), n)


def alpha_inv(i, j, n):
    f = ident(n)
    f[i] = (-j, i, j)
    return f


def check_mccool(n):
    A = lambda i, j: alpha_auto(i, j, n)
    Ai = lambda i, j: alpha_inv(i, j, n)
    idc = canon(ident(n), n)
    idx = range(1, n + 1)
    for i, j, k, l in itertools.permutations(idx, 4):
        if canon(comm(A(i, j), A(k, l), n, Ai(i, j), Ai(k, l)), n) != idc:
            return False, ('R1', i, j, k, l)
    for i, j, k in itertools.permutations(idx, 3):
        if canon(comm(A(i, j), A(k, j), n, Ai(i, j), Ai(k, j)), n) != idc:
            return False, ('R2', i, j, k)
        ab = compose(A(i, j), A(k, j), n)
        abi = compose(Ai(k, j), Ai(i, j), n)
        if canon(comm(ab, A(i, k), n, abi, Ai(i, k)), n) != idc:
            return False, ('R3', i, j, k)
    return True, None


def e_exponent(f, i, j):
    """Exponent sum of x_j in the reduced conjugator u, where f(x_i) = u x_i u^{-1} reduced."""
    w = red(f[i])
    m = len(w) // 2
    assert len(w) % 2 == 1 and w[m] == i and w[m + 1:] == inv(w[:m]), w
    return sum((1 if a > 0 else -1) for a in w[:m] if abs(a) == j)


def check_cabled(nmax):
    results = []
    for n in range(3, nmax + 1):  # alpha' in PLB_{n-1}, clone into PLB_n
        m = n - 1
        for k in range(1, m + 1):
            hat = lambda x: x if x < k else x + 1
            for p, q in itertools.permutations(range(1, m + 1), 2):
                w = alpha_word(p, q, m)
                got = canon(left(clone(w, k), n), n)
                if p != k and q != k:
                    pred = alpha_auto(hat(p), hat(q), n)
                elif q == k:
                    pred = compose(alpha_auto(hat(p), k + 1, n), alpha_auto(hat(p), k, n), n)
                else:
                    pred = compose(alpha_auto(k, hat(q), n), alpha_auto(k + 1, hat(q), n), n)
                if got != canon(pred, n):
                    return False, (n, k, p, q, got)
                f = left(clone(w, k), n)
                if e_exponent(f, k, k + 1) != 0 or e_exponent(f, k + 1, k) != 0:
                    return False, ('twist', n, k, p, q)
                results.append((n, k, p, q))
    return True, len(results)


def main():
    rng = random.Random(20260916)
    ok, info = check_lemma_a(rng)
    print("Lemma A on 400 random (n<=6, |w|<=12, k) triples:", ok, info)
    for n, L in ((3, 5), (4, 4)):
        print(f"cloning well defined on elements, LB_{n}, all words of length <= {L}:",
              check_well_defined(n, L))
    for n in (4, 5, 6):
        print(f"McCool relators R1-R3 hold in left form, n = {n}:", check_mccool(n))
    print("cabled McCool generators match the predicted formulas (n <= 7, all k, p, q), "
          "and e_{k,k+1} = e_{k+1,k} = 0 on them:", check_cabled(7))


if __name__ == "__main__":
    sys.exit(main())
