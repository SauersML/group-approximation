"""Nearest-neighbour SFTs on F_2 = <a, b> given by relations R_a, R_b on A = {0..n-1}.

A point is x : F_2 -> A with (x_g, x_{ga}) in R_a and (x_g, x_{gb}) in R_b for all g.
Every F_2-SFT is conjugate to one of these (higher block recoding along the tree).

Relations are stored as successor bitmasks: R[s] = bitmask of t with (s, t) in R.

Tests:
  essential(Ra, Rb)   -> restriction to the symbols that occur in some point
  is_si(Ra, Rb)       -> strong irreducibility = uniform path mixing along reduced words
  periodic(Ra, Rb)    -> exists a finite-orbit point  <=>  exists n >= 0, n != 0, which is
                         the vertex throughput of a circulation on R_a and of one on R_b (LP)
"""
import itertools
import numpy as np
from scipy.optimize import linprog


def transpose(R, n):
    T = [0] * n
    for s in range(n):
        for t in range(n):
            if R[s] >> t & 1:
                T[t] |= 1 << s
    return T


def restrict(R, keep, n):
    return [R[s] & keep if keep >> s & 1 else 0 for s in range(n)]


def essential(Ra, Rb, n):
    """Largest set E such that every s in E has an a-successor, a-predecessor,
    b-successor and b-predecessor in E. Symbols of points are exactly E (tree: extend greedily)."""
    E = (1 << n) - 1
    while True:
        Ta, Tb = transpose(Ra, n), transpose(Rb, n)
        newE = 0
        for s in range(n):
            if E >> s & 1 and Ra[s] & E and Ta[s] & E and Rb[s] & E and Tb[s] & E:
                newE |= 1 << s
        if newE == E:
            return E
        E = newE


def step(S, M):
    out = 0
    s = 0
    while S:
        if S & 1:
            out |= M[s]
        S >>= 1
        s += 1
    return out


def is_si(Ra, Rb, n, E=None, return_witness=False):
    """Letters 0=a, 1=a^-1, 2=b, 3=b^-1. SI iff from every singleton, the graph of
    (reachable set != E, last letter) states along reduced words is acyclic."""
    if E is None:
        E = essential(Ra, Rb, n)
    if E == 0:
        return (False, None) if return_witness else False
    Ra, Rb = restrict(Ra, E, n), restrict(Rb, E, n)
    Ms = [Ra, transpose(Ra, n), Rb, transpose(Rb, n)]
    inv = [1, 0, 3, 2]
    # global state graph over (set, last) with set != E
    color = {}
    for s0 in range(n):
        if not E >> s0 & 1:
            continue
        start = (1 << s0, -1)
        if (1 << s0) == E:
            continue
        stack = [(start, iter(range(4)))]
        path = [start]
        if color.get(start) == 2:
            continue
        color[start] = 1
        while stack:
            (S, last), it = stack[-1]
            advanced = False
            for x in it:
                if last >= 0 and x == inv[last]:
                    continue
                T = step(S, Ms[x])
                if T == E:
                    continue
                st = (T, x)
                c = color.get(st, 0)
                if c == 1:
                    if return_witness:
                        return False, (s0, [p for p in path], st)
                    return False
                if c == 0:
                    color[st] = 1
                    stack.append((st, iter(range(4))))
                    path.append(st)
                    advanced = True
                    break
            if not advanced:
                color[stack[-1][0]] = 2
                stack.pop()
                path.pop()
    return (True, None) if return_witness else True


def periodic(Ra, Rb, n):
    """LP feasibility: variables m_a[s,t] (s,t) in R_a, m_b[s,t] (s,t) in R_b, n_s.
    rows(m_a) = cols(m_a) = n = rows(m_b) = cols(m_b), sum n = 1, all >= 0."""
    ea = [(s, t) for s in range(n) for t in range(n) if Ra[s] >> t & 1]
    eb = [(s, t) for s in range(n) for t in range(n) if Rb[s] >> t & 1]
    nv = len(ea) + len(eb) + n
    rows = []
    rhs = []
    for E_, off in ((ea, 0), (eb, len(ea))):
        for v in range(n):
            r = np.zeros(nv)
            for i, (s, t) in enumerate(E_):
                if s == v:
                    r[off + i] += 1
            r[len(ea) + len(eb) + v] -= 1
            rows.append(r); rhs.append(0)
            r = np.zeros(nv)
            for i, (s, t) in enumerate(E_):
                if t == v:
                    r[off + i] += 1
            r[len(ea) + len(eb) + v] -= 1
            rows.append(r); rhs.append(0)
    r = np.zeros(nv); r[len(ea) + len(eb):] = 1
    rows.append(r); rhs.append(1)
    res = linprog(np.zeros(nv), A_eq=np.array(rows), b_eq=np.array(rhs),
                  bounds=[(0, None)] * nv, method="highs")
    return res.status == 0


def threshold_pair(w, phi, psi):
    """R_a = {(s,t): phi(t) > phi(s) - w(s)}, R_b = {(s,t): psi(t) < psi(s) - w(s)}.
    Every a-cycle has positive w-weight, every b-cycle negative: no periodic point.
    Every pair without periodic points is contained in such a pair (Farkas + Bellman-Ford)."""
    n = len(w)
    Ra = [sum(1 << t for t in range(n) if phi[t] > phi[s] - w[s]) for s in range(n)]
    Rb = [sum(1 << t for t in range(n) if psi[t] < psi[s] - w[s]) for s in range(n)]
    return Ra, Rb


def fills(E, mats, n):
    """From each singleton in E, apply the periodic sequence of matrices; True if all fill E."""
    for s in range(n):
        if not E >> s & 1:
            continue
        S = 1 << s
        seen = set()
        i = 0
        while S != E:
            key = (S, i % len(mats))
            if key in seen:
                return False
            seen.add(key)
            S = step(S, mats[i % len(mats)])
            i += 1
    return True


def cyc_word(Ra, Rb, n, E):
    """Cyclic reduced word (a, A=a^-1, b, B=b^-1) along which some reachable set never fills E."""
    ok, wit = is_si(Ra, Rb, n, E, return_witness=True)
    assert not ok
    s0, path, st = wit
    i = path.index(st)
    cyc = path[i + 1:] + [st]
    return "".join("aAbB"[x] for _, x in cyc)


def si_defect(Ra, Rb, n, E):
    """Number of reachable non-full (set, last-letter) states from which an infinite reduced
    word keeps the reachable set non-full. Zero iff SI (on the essential alphabet E)."""
    Ra, Rb = restrict(Ra, E, n), restrict(Rb, E, n)
    Ms = [Ra, transpose(Ra, n), Rb, transpose(Rb, n)]
    inv = [1, 0, 3, 2]
    succ = {}
    todo = [(1 << s, -1) for s in range(n) if E >> s & 1 and (1 << s) != E]
    while todo:
        st = todo.pop()
        if st in succ:
            continue
        S, last = st
        out = []
        for x in range(4):
            if last >= 0 and x == inv[last]:
                continue
            T = step(S, Ms[x])
            if T != E:
                out.append((T, x))
        succ[st] = out
        todo.extend(o for o in out if o not in succ)
    alive = set(succ)
    changed = True
    while changed:
        changed = False
        for st in list(alive):
            if not any(o in alive for o in succ[st]):
                alive.discard(st)
                changed = True
    return len(alive), len(succ)


def show(R, n):
    return " ".join(f"{s}->{''.join(str(t) for t in range(n) if R[s] >> t & 1)}" for s in range(n))
