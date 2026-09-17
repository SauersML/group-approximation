"""SAT census of finite-index overgroups of C1,m in Delta_(n,m).

Delta_(n,m) = C1,m *_(B0,n) C1',m (notation of
research/sl2-laurent-f2-amalgam-approximants-separate-the-vertex.md).
Generators (all involutions): w, u_0..u_m (u_j = e_12(t^j)), om = theta(w),
and nu_j = theta(u_j) for n+2 <= j <= m.  The other nu_j are forced by the
identifications of B0,n:
    nu_j = w u_(j+1) w      (0 <= j <= n-1)
    nu_j = om u_(j-1) om    (1 <= j <= n+1)
Relators: C1,m on (w,u), C1',m on (om,nu), and consistency on the overlap.

We search for an action on k points in which every generator of C1,m fixes
point 0 and a prescribed element g moves point 0.  Such an action exists iff
some subgroup of index <= k contains C1,m and excludes g.
"""
import sys, itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


class Enc:
    def __init__(self, k):
        self.k = k
        self.nv = 0
        self.cl = []

    def new(self):
        self.nv += 1
        return self.nv

    def perm(self, invol=False):
        k = self.k
        P = [[self.new() for _ in range(k)] for _ in range(k)]
        for i in range(k):
            self.exactly_one([P[i][j] for j in range(k)])
            self.exactly_one([P[j][i] for j in range(k)])
        if invol:
            for i in range(k):
                for j in range(i + 1, k):
                    self.cl.append([-P[i][j], P[j][i]])
                    self.cl.append([P[i][j], -P[j][i]])
        return P

    def exactly_one(self, lits):
        enc = CardEnc.equals(lits=lits, bound=1, top_id=self.nv,
                             encoding=EncType.seqcounter)
        self.nv = max(self.nv, enc.nv)
        self.cl.extend(enc.clauses)

    def compose(self, P, Q):
        """R = apply P then Q."""
        k = self.k
        R = self.perm()
        for i in range(k):
            for l in range(k):
                for j in range(k):
                    self.cl.append([-P[i][l], -Q[l][j], R[i][j]])
        return R

    def word(self, perms):
        R = perms[0]
        for P in perms[1:]:
            R = self.compose(R, P)
        return R

    def equal(self, P, Q):
        k = self.k
        for i in range(k):
            for j in range(k):
                self.cl.append([-P[i][j], Q[i][j]])
                self.cl.append([P[i][j], -Q[i][j]])

    def commute(self, P, Q):
        self.equal(self.compose(P, Q), self.compose(Q, P))

    def order3(self, P):
        P2 = self.compose(P, P)
        k = self.k
        for i in range(k):
            for j in range(k):  # P2 = P^-1
                self.cl.append([-P2[i][j], P[j][i]])
                self.cl.append([P2[i][j], -P[j][i]])


def build(n, m, k, target='om', trivial_top=True, drop=()):
    E = Enc(k)
    w = E.perm(True)
    u = [E.perm(True) for _ in range(m + 1)]
    om = E.perm(True)
    nu = {}
    for j in range(n + 2, m + 1):
        nu[j] = E.perm(True)
    # forced nu
    for j in range(0, n):
        nu.setdefault(j, E.word([w, u[j + 1], w]))
    for j in range(1, n + 2):
        c = E.word([om, u[j - 1], om])
        if j in nu:
            if ('rot', j) not in drop:
                E.equal(nu[j], c)  # rotation consistency
        else:
            nu[j] = c
    # C1,m relations
    if 'tri1' not in drop:
        E.order3(E.compose(w, u[0]))
    for a, b in itertools.combinations(range(m + 1), 2):
        if ('ucom', a, b) not in drop:
            E.commute(u[a], u[b])
    # C1',m relations
    if 'tri2' not in drop:
        E.order3(E.compose(om, nu[0]))
    for a, b in itertools.combinations(range(m + 1), 2):
        if (a < n and b < n) or (a >= 1 and b >= 1 and a <= n + 1 and b <= n + 1):
            continue  # conjugate of a commuting pair: automatic
        if ('com', a, b) not in drop:
            E.commute(nu[a], nu[b])
    # point 0 fixed by C1,m
    for idx, g in enumerate([w] + u):
        if ('free', idx) not in drop:  # idx 0 = w, idx j+1 = u_j
            E.cl.append([g[0][0]])
    if trivial_top:
        pass
    tgt = {'om': om}
    if target == 'om':
        E.cl.append([-om[0][0]])
    else:
        T = E.word([om] + [u[i] for i in target] + [om])  # om u_S om
        E.cl.append([-T[0][0]])
    return E, dict(w=w, u=u, om=om, nu=nu)


def standardize(E, gens):
    """Force a transitive, BFS-standard numbering: scanning rows c=0,1,...
    and generators in order, new points appear as 1,2,3,... in order."""
    k = E.k
    r = len(gens)
    positions = [(c, g) for c in range(k) for g in range(r)]
    L = len(positions)
    A = [[E.new() for _ in range(L)] for _ in range(k)]  # A[j][p]: seen at <= p
    for j in range(k):
        for p, (c, g) in enumerate(positions):
            lits = [gens[g][c][j]]
            if p > 0:
                lits.append(A[j][p - 1])
            E.cl.append([-A[j][p]] + lits)
            for x in lits:
                E.cl.append([A[j][p], -x])
    for j in range(1, k):
        E.cl.append([A[j][j * r - 1]])  # first seen in a row c < j
        if j >= 2:
            for p in range(L):
                E.cl.append([-A[j][p]] + ([A[j - 1][p - 1]] if p > 0 else []))
    return A


def decode(P, k, model):
    s = set(x for x in model if x > 0)
    return [next(j for j in range(k) if P[i][j] in s) for i in range(k)]


if __name__ == '__main__':
    n, m, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for k in range(2, kmax + 1):
        E, G = build(n, m, k)
        with Solver(name='cadical153', bootstrap_with=E.cl) as S:
            ok = S.solve()
            line = f'n={n} m={m} k={k} vars={E.nv} clauses={len(E.cl)} SAT={ok}'
            if ok:
                M = S.get_model()
                line += ' om=' + str(decode(G['om'], k, M))
                line += ' w=' + str(decode(G['w'], k, M))
                line += ' u=' + str([decode(x, k, M) for x in G['u']])
            print(line, flush=True)
            if ok:
                break
