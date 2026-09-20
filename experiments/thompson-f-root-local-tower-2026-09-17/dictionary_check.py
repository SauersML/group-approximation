"""Dictionary check for thompson-f-near-eigenvectors-carry-a-root-local-moore-tower.

Exact rational arithmetic, stdlib only.

Checks, for random pointed forests v = (T_0..T_{m-1}; i):
 (A) phi o x_k o phi^{-1} = s_k (k = 0, 1), where x_0, x_1 are Moore's generators on [0,1]
     (tree-diagram form) and s_0, s_1 are the PL(R) generators of the forest model.
 (B) The explicit tree diagram (L, R) built in Step 4 of the proof represents
     g = phi^{-1} o E(v) o phi, checked at many rational points.
 (C) After reducing (L, R), the subtree of L_g at the address 1^(k+1)0 has at most |T_(i+k)|
     leaves for every k >= 0, with equality (same shape) whenever T_(i+k) is nontrivial.
 (D) Moves are right multiplications in Moore's convention after inversion:
     psi(E(v')) = psi(E(v)) o x_1 for a merge, psi(E(v')) = psi(E(v)) o x_0 for pointer right.
"""
from fractions import Fraction as Fr
import math
import random

random.seed(20260917)

# ---------- binary strings <-> dyadic intervals ----------

def interval(u):
    a = Fr(0)
    for j, c in enumerate(u):
        if c == '1':
            a += Fr(1, 2 ** (j + 1))
    return a, a + Fr(1, 2 ** len(u))


def apply_diagram(L, R, x):
    for s, t in zip(L, R):
        a, b = interval(s)
        if a <= x < b or (x == b == 1):
            c, d = interval(t)
            return c + (x - a) * (d - c) / (b - a)
    raise ValueError(x)

# ---------- phi : (0,1) -> R ----------

def phi(x):
    if x == Fr(1, 2):
        return Fr(0)
    if x > Fr(1, 2):
        k = 1
        while not (1 - Fr(1, 2 ** k) <= x < 1 - Fr(1, 2 ** (k + 1))):
            k += 1
        return (k - 1) + (x - (1 - Fr(1, 2 ** k))) * 2 ** (k + 1)
    k = 1
    while not (Fr(1, 2 ** (k + 1)) <= x < Fr(1, 2 ** k)):
        k += 1
    return -k + (x - Fr(1, 2 ** (k + 1))) * 2 ** (k + 1)


def phi_inv(t):
    if t >= 0:
        k = math.floor(t) + 1
        return 1 - Fr(1, 2 ** k) + (t - (k - 1)) / 2 ** (k + 1)
    k = -math.floor(t)
    return Fr(1, 2 ** (k + 1)) + (t + k) / 2 ** (k + 1)


def unit_to_string(a):
    """[a, a+1] <-> binary address."""
    return '1' * (a + 1) + '0' if a >= 0 else '0' * (-a) + '1'

# ---------- forest model ----------

def size(T):
    return 1 if T is None else size(T[0]) + size(T[1])


def h(T, s):
    if T is None:
        return s
    if s <= Fr(1, 2):
        return h(T[0], 2 * s)
    return size(T[0]) + h(T[1], 2 * s - 1)


def leaves(T, pre=''):
    if T is None:
        return [pre]
    return leaves(T[0], pre + '0') + leaves(T[1], pre + '1')


def E(state, t):
    trees, i = state
    m = len(trees)
    n = sum(size(T) for T in trees)
    k = math.floor(t)
    j = i + k
    if j < 0:
        return j + (t - k)
    if j >= m:
        return n + j - m + (t - k)
    a = sum(size(trees[q]) for q in range(j))
    return a + h(trees[j], t - k)


def s0(t):
    return t + 1


def s1(t):
    if t <= 0:
        return t
    if t <= 1:
        return 2 * t
    return t + 1

X0 = (['00', '01', '1'], ['0', '10', '11'])
X1 = (['0', '100', '101', '11'], ['0', '10', '110', '111'])


def g_of(state, x):
    return phi_inv(E(state, phi(x)))

# ---------- the explicit diagram of Step 4 ----------

def diagram(state, N):
    trees, i = state
    m = len(trees)
    n = sum(size(T) for T in trees)
    L = ['0' * (N + 1)]
    Rr = ['0' * (N - i + 1)]
    for k in range(-N, N):
        j = i + k
        T = trees[j] if 0 <= j < m else None
        u = unit_to_string(k)
        if 0 <= j < m:
            a = sum(size(trees[q]) for q in range(j))
        elif j < 0:
            a = j
        else:
            a = n + j - m
        for q, w in enumerate(leaves(T)):
            L.append(u + w if T is not None else u)
            Rr.append(unit_to_string(a + q))
    L.append('1' * (N + 1))
    Rr.append('1' * (N + n + i - m + 1))
    return L, Rr


def reduce(L, R):
    L, R = list(L), list(R)
    changed = True
    while changed:
        changed = False
        for q in range(len(L) - 1):
            s, s2, t, t2 = L[q], L[q + 1], R[q], R[q + 1]
            if (s[:-1] == s2[:-1] and s[-1] == '0' and s2[-1] == '1'
                    and t[:-1] == t2[:-1] and t[-1] == '0' and t2[-1] == '1'):
                L[q:q + 2] = [s[:-1]]
                R[q:q + 2] = [t[:-1]]
                changed = True
                break
    return L, R


def subtree_leaves(L, u):
    return [s[len(u):] for s in L if s.startswith(u)]


def random_tree(nleaves):
    if nleaves == 1:
        return None
    a = random.randint(1, nleaves - 1)
    return (random_tree(a), random_tree(nleaves - a))


def random_state():
    m = random.randint(1, 7)
    trees = [random_tree(random.choice([1, 1, 2, 3, 4, 6, 9])) for _ in range(m)]
    return trees, random.randint(0, m - 1)


def rand_point():
    return Fr(random.randint(1, 2 ** 20 - 1), 2 ** 20)


def main():
    # (A)
    for _ in range(3000):
        t = Fr(random.randint(-4000, 4000), random.choice([1, 2, 4, 8, 16, 1024]))
        assert phi(phi_inv(t)) == t
        assert phi(apply_diagram(*X0, phi_inv(t))) == s0(t)
        assert phi(apply_diagram(*X1, phi_inv(t))) == s1(t)
    print('(A) phi x_k phi^-1 = s_k on 3000 points: ok')

    nstates = 0
    nsub = 0
    nexact = 0
    for _ in range(400):
        state = random_state()
        trees, i = state
        m = len(trees)
        N = max(i, m - i) + 2
        L, R = diagram(state, N)
        for _ in range(60):
            x = rand_point()
            assert apply_diagram(L, R, x) == g_of(state, x), (state, x)
        Lr, Rr = reduce(L, R)
        for _ in range(20):
            x = rand_point()
            assert apply_diagram(Lr, Rr, x) == g_of(state, x)
        for k in range(0, N):
            j = i + k
            T = trees[j] if 0 <= j < m else None
            sub = subtree_leaves(Lr, unit_to_string(k))
            assert len(sub) <= size(T), (state, k, sub)
            nsub += 1
            if T is not None:
                assert sub == leaves(T), (state, k, sub, leaves(T))
                nexact += 1
        # (D) moves
        if i + 1 < m:
            merged = (trees[:i] + [(trees[i], trees[i + 1])] + trees[i + 2:], i)
            right = (trees, i + 1)
            for _ in range(20):
                x = rand_point()
                assert g_of(merged, x) == g_of(state, apply_diagram(*X1, x))
                assert g_of(right, x) == g_of(state, apply_diagram(*X0, x))
        nstates += 1
    print(f'(B) explicit diagram represents phi^-1 E(v) phi on {nstates} random states: ok')
    print(f'(C) |L_g / 1^(k+1)0| <= |T_(i+k)| on {nsub} (state, k) pairs; '
          f'equal shape on all {nexact} pairs with T_(i+k) nontrivial: ok')
    print('(D) merge = right mult by x_1, pointer right = right mult by x_0 (after psi): ok')


if __name__ == '__main__':
    main()
