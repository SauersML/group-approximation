"""Arcs in the 4-punctured disc (punctures q,a,b,t = 0,1,2,3 on a horizontal line), cut along vertical rays.

Model.  D is a disc with punctures 0..3 on a horizontal line and two boundary points: d0 at the bottom, d1 at the
top-left.  From each puncture k a ray rho_k goes straight up to the top boundary.  P = D minus the rays is a disc.
An arc is recorded by its crossing word with the rays: letter +(k+1) is a crossing of rho_k from right to left,
-(k+1) from left to right.  Its pieces are chords of P.

  x-arcs (type X = <s1,s2> vertices): arcs from t (=3) to d0.  gamma0 = straight down, word ().
  y-arcs (type Y = <s2,s3> vertices): arcs from q (=0) to d1.  delta0 = straight left-up, word ().

pi_1(D - punctures, d0) = F<x0..x3>, x_k = up the right of k, over rho_k leftwards, back.  The arc from d0 to p with
crossing word w corresponds to the element w x_p w^-1.  Braids act by the Artin action (convention checked against
curver in selftest()).  y-arcs are transported to d0 along the left boundary, which crosses no ray, so the same
correspondence holds for them with v x_q v^-1.

place(arcs) puts the chords of several arcs in pairwise minimal position (lexicographic itinerary rule), and
regions() decides which boundary markers (puncture q, point d1) lie in one component of D minus the arcs.
"""
import functools

import os
N = int(os.environ.get("ARCS_N", "4"))
# ccw cyclic order of the slots of dP
SLOTS = ['d0']
for k in range(N - 1, -1, -1):
    SLOTS += [('R', k), ('P', k), ('L', k)]
SLOTS += ['d1']
IDX = {s: i for i, s in enumerate(SLOTS)}
NS = len(SLOTS)


def red(w):
    out = []
    for c in w:
        if out and out[-1] == -c:
            out.pop()
        else:
            out.append(c)
    return out


def inv(w):
    return [-c for c in reversed(w)]


SIGN = -1


def artin(i, sign=1):
    """automorphism of F_4 for sigma_i^sign (i = 1..3 swaps punctures i-1, i). returns dict gen->word.
    Loops x_k are ccw, based at the bottom, so the boundary loop is x3 x2 x1 x0 (path order); both maps fix it."""
    a, b = i, i + 1   # letters for x_{i-1}, x_i
    if sign * SIGN == 1:
        return {a: [b], b: [b, a, -b]}
    else:
        return {b: [a], a: [-a, b, a]}


def apply_aut(aut, w):
    out = []
    for c in w:
        if abs(c) in aut:
            img = aut[abs(c)]
            out += img if c > 0 else inv(img)
        else:
            out.append(c)
    return red(out)


def act(braid, w):
    """braid = list of signed generator indices (+-1..+-3), read as a composition of maps:
    the RIGHTMOST letter is applied first (as curver does for 's_1.s_2')."""
    for g in reversed(braid):
        w = apply_aut(artin(abs(g), 1 if g > 0 else -1), w)
    return w


def arc_word(braid, p):
    """crossing word and end puncture of braid(standard arc from base to p), standard element x_p"""
    e = act(braid, [p + 1])
    # e = w x_p' w^-1 reduced
    m = len(e) // 2
    pe = e[m]
    assert pe > 0 and red(e[:m] + [pe] + inv(e[:m])) == e, e
    w = e[:m]
    while w and abs(w[-1]) == pe:
        w = w[:-1]
    return tuple(w), pe - 1


class Arc:
    def __init__(self, start, word, end):
        self.start, self.word, self.end = start, tuple(word), end   # start/end are slots

    def elem(self, j, tau):
        """element reached when moving from position j in direction tau; positions: -1=start, 0..m-1 crossings, m=end"""
        jj = j + tau
        m = len(self.word)
        if jj < 0:
            return ('E', self.start)
        if jj >= m:
            return ('E', self.end)
        c = self.word[jj] * tau
        k = abs(c) - 1
        return ('X', k, 'R' if c > 0 else 'L', jj)   # arrival side


def xarc(braid):
    w, pe = arc_word(braid, N - 1)
    return Arc('d0', w, ('P', pe))


def yarc(braid):
    w, pe = arc_word(braid, 0)
    return Arc('d1', w, ('P', pe))


class Placement:
    def __init__(self, arcs):
        self.arcs = arcs
        self.memo = {}

    def dep_cmp(self, D, A, B):
        """A=(arc,j,tau), B likewise, both departing from slot D (a ray side or an endpoint slot).
        return True if A's point is ccw-before B's point on D (non-crossing preference), None if undetermined"""
        key = (D, A, B)
        if key in self.memo:
            return self.memo[key]
        self.memo[key] = None   # guard against cycles
        aA, jA, tA = A
        aB, jB, tB = B
        eA = self.arcs[aA].elem(jA, tA)
        eB = self.arcs[aB].elem(jB, tB)
        sA = eA[1] if eA[0] == 'E' else (eA[2], eA[1])
        sB = eB[1] if eB[0] == 'E' else (eB[2], eB[1])
        res = None
        if sA != sB:
            oA = (IDX[sA] - IDX[D]) % NS
            oB = (IDX[sB] - IDX[D]) % NS
            res = oB < oA
        elif eA[0] == 'X':
            side, k = eA[2], eA[1]
            dside = 'L' if side == 'R' else 'R'
            A2, B2 = (aA, eA[3], tA), (aB, eB[3], tB)
            r = self.dep_cmp((dside, k), A2, B2)   # ccw-before on the departure side
            if r is not None:
                # convert to heights: on L ccw = up, on R ccw = down
                A_lower = r if dside == 'L' else (not r)
                # e_B ccw-before e_A on arrival side
                cond = (not A_lower) if side == 'L' else A_lower
                res = cond
        self.memo[key] = res
        return res

    def height_cmp(self, k, A, B):
        """A,B crossings (arc,j) of ray k. return True if A is lower. Uses forward then backward itinerary."""
        def orient(X):
            a, j = X
            c = self.arcs[a].word[j]
            return (a, j, 1 if c > 0 else -1)   # travel so that crossing is R->L
        oA, oB = orient(A), orient(B)
        f = self.dep_cmp(('L', k), oA, oB)          # departing on L (ccw = up)
        fl = None if f is None else f               # A lower iff ccw-before on L
        rA, rB = (oA[0], oA[1], -oA[2]), (oB[0], oB[1], -oB[2])
        b = self.dep_cmp(('R', k), rA, rB)          # departing on R (ccw = down)
        bl = None if b is None else (not b)
        if fl is not None and bl is not None and fl != bl:
            # forced crossing: decide consistently along the whole parallel run, by the travel direction of a
            # reference strand (lower arc index, or lower position on the same arc) in its own increasing order
            ref = oA if (A[0], A[1]) < (B[0], B[1]) else oB
            return fl if ref[2] == 1 else bl
        if fl is not None:
            return fl
        if bl is not None:
            return bl
        return A < B

    def place(self):
        """initial placement from the itinerary comparator (pairwise minimal for two arcs)"""
        self.order = {}
        for k in range(N):
            pts = [(a, j) for a, arc in enumerate(self.arcs) for j, c in enumerate(arc.word) if abs(c) - 1 == k]
            pts.sort(key=functools.cmp_to_key(lambda A, B: -1 if self.height_cmp(k, A, B) else 1))
            self.order[k] = pts
        self.fanlist = {}
        ends = {}
        for a, arc in enumerate(self.arcs):
            ends.setdefault(arc.start, []).append((a, -1, 1))
            ends.setdefault(arc.end, []).append((a, len(arc.word), -1))
        for s, L in ends.items():
            L.sort(key=functools.cmp_to_key(lambda A, B: -1 if (self.dep_cmp(s, A, B) or (self.dep_cmp(s, A, B) is None and A < B)) else 1))
            self.fanlist[s] = [A[0] for A in L]
        return self.build()

    def build(self):
        self.height = {}
        for k, pts in self.order.items():
            for h, P in enumerate(pts):
                self.height[P] = h + 1
            self.height[('n', k)] = len(pts)
        self.fan = {}
        for s, L in self.fanlist.items():
            for i, a in enumerate(L):
                self.fan[(s, a)] = i
        self.chords = []   # (posA, posB, arc)
        for a, arc in enumerate(self.arcs):
            pts = [self.pos_end(arc.start, a)]
            for j, c in enumerate(arc.word):
                k = abs(c) - 1
                h = self.height[(a, j)]
                arr, dep = ('R', 'L') if c > 0 else ('L', 'R')
                pts.append(self.pos_ray(arr, k, h))
                pts.append(self.pos_ray(dep, k, h))
            pts.append(self.pos_end(arc.end, a))
            for i in range(0, len(pts), 2):
                self.chords.append((pts[i], pts[i + 1], a))
        return self

    def excess(self, target):
        cnt = self.crossings()
        e = 0
        for key, v in cnt.items():
            e += v - (0 if key[0] == key[1] else target.get(key, 0))
        return e, cnt

    def minimize(self, target, rounds=200):
        """hill-climb by adjacent swaps (on rays and in endpoint fans) until every pair meets its target
        (pairwise minimal intersection) and no arc self-crosses. returns True on success."""
        best, cnt = self.excess(target)
        for _ in range(rounds):
            if best == 0 and all(cnt.get((a, b), 0) == target.get((a, b), 0)
                                 for a in range(len(self.arcs)) for b in range(a + 1, len(self.arcs))):
                return True
            improved = False
            moves = [('r', k, i) for k, L in self.order.items() for i in range(len(L) - 1)]
            moves += [('f', s, i) for s, L in self.fanlist.items() for i in range(len(L) - 1)]
            for mv in moves:
                L = self.order[mv[1]] if mv[0] == 'r' else self.fanlist[mv[1]]
                i = mv[2]
                L[i], L[i + 1] = L[i + 1], L[i]
                self.build()
                e, c2 = self.excess(target)
                if e < best:
                    best, cnt, improved = e, c2, True
                    break
                L[i], L[i + 1] = L[i + 1], L[i]
            self.build()
            if not improved:
                return False
        return False

    def pos_ray(self, side, k, h):
        n = self.height[('n', k)]
        sub = h if side == 'L' else (n + 1 - h)   # ccw sub-order
        return (IDX[(side, k)], sub)

    def pos_end(self, s, a):
        return (IDX[s], self.fan[(s, a)] + 1)

    def crossings(self):
        """number of crossings between chords of arcs a<b, and within an arc"""
        cnt = {}

        def between(x, a, b):   # x strictly inside ccw arc from a to b
            return (a < x < b) if a < b else (x > a or x < b)
        for i, (p, q, a) in enumerate(self.chords):
            for (r, s, b) in self.chords[i + 1:]:
                if len({p, q, r, s}) < 4:
                    continue
                if between(r, p, q) != between(s, p, q):
                    key = (min(a, b), max(a, b))
                    cnt[key] = cnt.get(key, 0) + 1
        return cnt

    def regions(self, markers):
        """markers: list of slots (('P',k) or 'd1' or 'd0'). returns list of component labels, one per marker."""
        # all chord endpoint positions, sorted cyclically
        eps = sorted({p for c in self.chords for p in c[:2]})
        # a boundary 'item' is either a ray-side interval (side,k,i) or a marker; locate its gap
        def gap_of(pos):
            # gap index g means between eps[g-1] and eps[g] (cyclically); pos is a non-endpoint position
            for g, e in enumerate(eps):
                if pos < e:
                    return g
            return 0
        # items: ray-side intervals i = 0..n (between heights i and i+1)
        par = {}

        def find(x):
            while par.setdefault(x, x) != x:
                par[x] = par[par[x]]
                x = par[x]
            return x

        def union(x, y):
            par[find(x)] = find(y)
        ngap = max(1, len(eps))
        if not eps:
            return [0] * len(markers)
        # same region inside P: no chord separates the two gaps
        def mid(g):   # representative position of gap g
            lo = eps[g - 1] if g > 0 else (eps[-1][0] - NS, eps[-1][1])
            return (lo, eps[g % len(eps)])

        def sep(g1, g2):
            for (p, q, a) in self.chords:
                x1 = self._inside_gap(g1, p, q, eps)
                x2 = self._inside_gap(g2, p, q, eps)
                if x1 != x2:
                    return True
            return False
        G = len(eps)
        for g1 in range(G):
            for g2 in range(g1 + 1, G):
                if not sep(g1, g2):
                    union(('g', g1), ('g', g2))
        # gluing across rays
        for k in range(N):
            n = self.height[('n', k)]
            for i in range(n + 1):
                # interval between heights i and i+1: on L sub-position between i and i+1 -> pos (IDX, i+0.5)
                pl = (IDX[('L', k)], i + 0.5)
                pr = (IDX[('R', k)], (n + 1 - (i + 1)) + 0.5)
                union(('g', gap_of(pl)), ('g', gap_of(pr)))
        out = []
        for m in markers:
            if m == 'd1' or m == 'd0' or m[0] == 'P':
                cnt = sum(1 for c in self.chords for p in c[:2] if p[0] == IDX[m])
                if cnt:
                    raise ValueError('marker %r is a chord endpoint' % (m,))
                pos = (IDX[m], 0.5)
            out.append(find(('g', gap_of(pos))))
        return out

    @staticmethod
    def _inside_gap(g, p, q, eps):
        # is gap g (between eps[g-1], eps[g]) strictly inside the ccw arc p->q ?
        G = len(eps)
        a = eps[g - 1] if g > 0 else eps[-1]
        # the gap lies just after a; it is inside (p,q) iff a is in [p, q) ccw
        if p < q:
            return p <= a < q
        return a >= p or a < q


def pair_target(arcs):
    """pairwise intersection numbers from two-arc placements (validated against curver by selftest.py)"""
    t = {}
    for a in range(len(arcs)):
        for b in range(a + 1, len(arcs)):
            c = Placement([arcs[a], arcs[b]]).place().crossings()
            if c.get((0, 0)) or c.get((1, 1)):
                raise ValueError('self-crossing in two-arc placement')
            t[(a, b)] = c.get((0, 1), 0)
    return t


def tight(arcs, target=None):
    """a simultaneous placement in which every pair is in minimal position, or None"""
    target = pair_target(arcs) if target is None else target
    P = Placement(list(arcs)).place()
    return P if P.minimize(target) else None


def outer_set(arcs, punct=(0, 1, 2)):
    """punctures in the region of D minus the arcs that contains d1 (None if no tight placement found)"""
    P = tight(arcs)
    if P is None:
        return None
    r = P.regions([('P', p) for p in punct] + ['d1'])
    return frozenset(p for p, x in zip(punct, r) if x == r[-1])
