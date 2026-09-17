#!/usr/bin/env python3
"""Calibration for solvable-polynomial-automata-reduce-to-kaplansky.

Alphabets Q = V x| T with V = F_p^d minimal normal and T cyclic acting by a matrix M:
  S3 = F_3 x| Z/2  (M = -1),   A4 = F_2^2 x| Z/3  (M = [[0,1],[1,1]]).
Hosts G = Z/n.  A Q-polynomial automaton is tau(x)(g) = w(x(g+m_1),...,x(g+m_k)), w in Q*F_k.

Checks:
 (F) fibration formula: the V-part of w is  sum_j Coef_j(t) v_j + off(t), with Coef_j(t) in the
     F_p-span of rho(T), computed by the prefix rules
        +x_j : Coef_j += M^acc,           acc += t_j
        -x_j : Coef_j -= M^acc M^(-t_j),  acc -= t_j
        c=(v0,u): off += M^acc v0,        acc += u
     and the T-part is sum_j eps_j t_j + const  (compared with direct evaluation, all t-patterns).
 (B) on every host: tau bijective  <=>  sigma (the T-automaton) bijective and every fibre L_t
     bijective (brute force over Q^n), and tau bijective => constant fibres L_{t=b} bijective.
     Also counts words where sigma and the constant fibre L_0 are bijective but tau is not
     (so injectivity of tau is a genuine hypothesis of the dichotomy step on finite hosts).
 (S) the seed criterion (alpha unit mod exponent of Q^ab) vs truth; reproduces
     tau(x)(g) = x(g)^2 x(g+1)^-1 over S3 on Z/2, with constant fibre 2 - t non-unit in F_3[Z/2].
 (R) S3 realizers: p(x) = x^3 r x r x = r^{s(x)},  v(x) = x p(x) = t^{a(x)};
     tau_beta(x)(g) = v(x(g)) prod_h p(x(g+h))^{beta_h}  gives (a,s) -> (a, s*beta);
     tau_lam(x)(g)  = prod_h v(x(g+h))^{lam_h} p(x(g))   gives (a,s) -> (a*lam, s).
"""
import itertools
import random
import sys


def matmul(A, B, p):
    n, m, r = len(A), len(B), len(B[0])
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(m)) % p for j in range(r)) for i in range(n))


def matpow(M, e, p):
    d = len(M)
    R = tuple(tuple(int(i == j) for j in range(d)) for i in range(d))
    for _ in range(e):
        R = matmul(R, M, p)
    return R


def matadd(A, B, p, sgn=1):
    return tuple(tuple((A[i][j] + sgn * B[i][j]) % p for j in range(len(A[0]))) for i in range(len(A)))


def apply(M, v, p):
    return tuple(sum(M[i][k] * v[k] for k in range(len(v))) % p for i in range(len(M)))


def rank_mod_p(rows, p):
    rows = [list(r) for r in rows]
    rk, ncol = 0, (len(rows[0]) if rows else 0)
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], p - 2, p)
        rows[rk] = [(x * inv) % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk


class SemiDirect:
    def __init__(self, name, p, d, M, tord):
        self.name, self.p, self.d, self.M, self.tord = name, p, d, M, tord
        self.Mp = [matpow(M, e, p) for e in range(tord)]
        self.elems = [(v, t) for v in itertools.product(range(p), repeat=d) for t in range(tord)]
        self.idx = {e: i for i, e in enumerate(self.elems)}
        self.one = (tuple([0] * d), 0)
        # exponent of Q^ab: T-part order times V-part order if V is central
        central = all(self.Mp[1][i][j] == int(i == j) for i in range(d) for j in range(d))
        self.eab = tord * (p if central else 1)

    def mul(self, x, y):
        (v, t), (w, u) = x, y
        mw = apply(self.Mp[t], w, self.p)
        return (tuple((a + b) % self.p for a, b in zip(v, mw)), (t + u) % self.tord)

    def inv(self, x):
        v, t = x
        ti = (-t) % self.tord
        mv = apply(self.Mp[ti], v, self.p)
        return (tuple((-a) % self.p for a in mv), ti)


S3 = SemiDirect('S3', 3, 1, ((2,),), 2)
A4 = SemiDirect('A4', 2, 2, ((0, 1), (1, 1)), 3)


def evaluate(Q, word, xs):
    acc = Q.one
    for L in word:
        if L[0] == 'x':
            _, j, e = L
            acc = Q.mul(acc, xs[j] if e == 1 else Q.inv(xs[j]))
        else:
            acc = Q.mul(acc, L[1])
    return acc


def fibration(Q, word, k, ts):
    p, d = Q.p, Q.d
    zero = tuple(tuple(0 for _ in range(d)) for _ in range(d))
    coef = [zero] * k
    off = tuple([0] * d)
    acc = 0
    tsum = 0
    for L in word:
        if L[0] == 'x':
            _, j, e = L
            if e == 1:
                coef[j] = matadd(coef[j], Q.Mp[acc], p)
                acc = (acc + ts[j]) % Q.tord
            else:
                coef[j] = matadd(coef[j], matmul(Q.Mp[acc], Q.Mp[(-ts[j]) % Q.tord], p), p, -1)
                acc = (acc - ts[j]) % Q.tord
        else:
            v0, u = L[1]
            off = tuple((a + b) % p for a, b in zip(off, apply(Q.Mp[acc], v0, p)))
            acc = (acc + u) % Q.tord
    return coef, off, acc


def random_word(Q, k, length, rng):
    w = []
    for _ in range(length):
        if rng.random() < 0.25:
            w.append(('c', rng.choice(Q.elems)))
        else:
            w.append(('x', rng.randrange(k), rng.choice((1, -1))))
    return w


def check_fibration(Q, word, k, rng):
    for ts in itertools.product(range(Q.tord), repeat=k):
        coef, off, tpart = fibration(Q, word, k, ts)
        for _ in range(4):
            vs = [tuple(rng.randrange(Q.p) for _ in range(Q.d)) for _ in range(k)]
            val = evaluate(Q, word, [(vs[j], ts[j]) for j in range(k)])
            pred = off
            for j in range(k):
                pred = tuple((a + b) % Q.p for a, b in zip(pred, apply(coef[j], vs[j], Q.p)))
            # T-part must be independent of vs and affine in ts
            if val[0] != pred or val[1] != tpart:
                return False
    return True


def tau_table(Q, word, mem, n):
    k = len(mem)
    out = {}
    for conf in itertools.product(range(len(Q.elems)), repeat=n):
        x = [Q.elems[i] for i in conf]
        y = tuple(Q.idx[evaluate(Q, word, [x[(g + m) % n] for m in mem])] for g in range(n))
        out[conf] = y
    return out


def fibre_matrix(Q, word, mem, n, tconf):
    k = len(mem)
    d, p = Q.d, Q.p
    rows = [[0] * (d * n) for _ in range(d * n)]
    for g in range(n):
        coef, _, _ = fibration(Q, word, k, [tconf[(g + m) % n] for m in mem])
        for j, m in enumerate(mem):
            h = (g + m) % n
            for i in range(d):
                for c in range(d):
                    rows[g * d + i][h * d + c] = (rows[g * d + i][h * d + c] + coef[j][i][c]) % p
    return rows


def sigma_bijective(Q, word, mem, n):
    # T-part is sum_j eps_j t(g+m_j) + const over Z/tord (tord prime here)
    eps = [0] * len(mem)
    for L in word:
        if L[0] == 'x':
            eps[L[1]] += L[2]
    rows = [[0] * n for _ in range(n)]
    for g in range(n):
        for j, m in enumerate(mem):
            rows[g][(g + m) % n] = (rows[g][(g + m) % n] + eps[j]) % Q.tord
    return rank_mod_p(rows, Q.tord) == n, eps


def run(seed, trials_per):
    rng = random.Random(seed)
    lines = []
    stats = {}
    for Q, hosts in ((S3, (1, 2, 3, 4)), (A4, (1, 2, 3))):
        st = dict(words=0, fib_ok=0, bij=0, pred_match=0, const_fibres_ok=0,
                  sigma_L0_bij_but_tau_not=0, seed_crit_wrong=0)
        for n in hosts:
            for _ in range(trials_per):
                k = rng.randint(1, min(3, n + 1))
                mem = [rng.randrange(n) for _ in range(k)]
                word = random_word(Q, k, rng.randint(1, 7), rng)
                st['words'] += 1
                if check_fibration(Q, word, k, rng):
                    st['fib_ok'] += 1
                tab = tau_table(Q, word, mem, n)
                bij = len(set(tab.values())) == len(tab)
                sb, eps = sigma_bijective(Q, word, mem, n)
                all_fib = all(rank_mod_p(fibre_matrix(Q, word, mem, n, tc), Q.p) == Q.d * n
                              for tc in itertools.product(range(Q.tord), repeat=n))
                const_fib = all(rank_mod_p(fibre_matrix(Q, word, mem, n, [b] * n), Q.p) == Q.d * n
                                for b in range(Q.tord))
                L0 = rank_mod_p(fibre_matrix(Q, word, mem, n, [0] * n), Q.p) == Q.d * n
                st['bij'] += bij
                st['pred_match'] += (bij == (sb and all_fib))
                if bij:
                    st['const_fibres_ok'] += const_fib
                if sb and L0 and not bij:
                    st['sigma_L0_bij_but_tau_not'] += 1
                # seed criterion: alpha = sum eps_j m_j unit in (Z/eab)[Z/n]  <=> circulant invertible mod eab
                eab = Q.eab
                rows = [[0] * n for _ in range(n)]
                for g in range(n):
                    for j, m in enumerate(mem):
                        rows[g][(g + m) % n] = (rows[g][(g + m) % n] + eps[j]) % eab
                ok = all(rank_mod_p([[x % q for x in r] for r in rows], q) == n
                         for q in {2, 3, 5, 7} if eab % q == 0)
                if ok != bij:
                    st['seed_crit_wrong'] += 1
        stats[Q.name] = st
        lines.append(f"{Q.name}: {st}")
    return lines, stats


def seed_example():
    Q = S3
    word = [('x', 0, 1), ('x', 0, 1), ('x', 1, -1)]
    mem, n = [0, 1], 2
    tab = tau_table(Q, word, mem, n)
    bij = len(set(tab.values())) == len(tab)
    coef, off, _ = fibration(Q, word, 2, [0, 0])
    L0 = fibre_matrix(Q, word, mem, n, [0, 0])
    return (f"seed example x(g)^2 x(g+1)^-1 over S3 on Z/2: bijective={bij}, images={len(set(tab.values()))}/36, "
            f"constant-fibre coefficients (site0,site1)=({coef[0][0][0]},{coef[1][0][0]}) i.e. 2+2t = 2-t, "
            f"L0 rank={rank_mod_p(L0, 3)}/2; seed criterion alpha=2-t mod 2 = t is a unit of F_2[Z/2]")


def realizers():
    Q = S3
    r = ((0,), 1)
    p_word = [('x', 0, 1)] * 3 + [('c', r), ('x', 0, 1), ('c', r), ('x', 0, 1)]
    v_word = [('x', 0, 1)] + p_word
    ok_p = all(evaluate(Q, p_word, [x]) == ((0,), x[1]) for x in Q.elems)
    ok_v = all(evaluate(Q, v_word, [x]) == (x[0], 0) for x in Q.elems)
    out = [f"p(x)=x^3 r x r x equals r^s on all of S3: {ok_p}", f"v(x)=x p(x) equals t^a on all of S3: {ok_v}"]
    rng = random.Random(7)
    good_b = good_l = 0
    tot = 0
    for n in (2, 3, 4):
        for _ in range(6):
            beta = [rng.randrange(2) for _ in range(n)]
            lam = [rng.randrange(3) for _ in range(n)]
            wb = v_word[:]  # variable 0 = x(g)
            mem_b = [0] + list(range(n))
            for h in range(n):
                if beta[h]:
                    wb += [('x', 1 + h, 1)] * 3 + [('c', r), ('x', 1 + h, 1), ('c', r), ('x', 1 + h, 1)]
            wl = []
            mem_l = list(range(n)) + [0]
            for h in range(n):
                wl += ([('x', h, 1)] + [('x', h, 1)] * 3 + [('c', r), ('x', h, 1), ('c', r), ('x', h, 1)]) * lam[h]
            wl += [('x', n, 1)] * 3 + [('c', r), ('x', n, 1), ('c', r), ('x', n, 1)]
            for conf in itertools.product(range(6), repeat=n):
                x = [Q.elems[i] for i in conf]
                yb = [evaluate(Q, wb, [x[(g + m) % n] for m in mem_b]) for g in range(n)]
                yl = [evaluate(Q, wl, [x[(g + m) % n] for m in mem_l]) for g in range(n)]
                eb = [(x[g][0], sum(beta[h] * x[(g + h) % n][1] for h in range(n)) % 2) for g in range(n)]
                el = [((sum(lam[h] * x[(g + h) % n][0][0] for h in range(n)) % 3,), x[g][1]) for g in range(n)]
                good_b += (yb == eb)
                good_l += (yl == el)
                tot += 1
    out.append(f"tau_beta = (a, s*beta) on {tot} (host,beta,config) cases: {good_b}/{tot}")
    out.append(f"tau_lam  = (a*lam, s) on {tot} (host,lam,config) cases: {good_l}/{tot}")
    return out


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    print(f"seed={seed} trials_per_host={trials}")
    print(seed_example())
    for l in realizers():
        print(l)
    lines, _ = run(seed, trials)
    for l in lines:
        print(l)
