#!/usr/bin/env python3
"""Machine check of the three-ray edge layer of Theorem A (H_3 reduction to five families).

Checks, for all 8 route functions c on rays {1,2,3} and all edges of depth <= R0:

  Part A  every edge relation (E1)-(E3) of Sec. 4 of the six-ray note is derived from
          relators of Q (trivial words of length <= 40) plus AT MOST ONE literal
          five-family relator (F_3, B_3, C_3) of index <= depth, with O(R) Q-steps;
          (E2)(v) (two disjoint top edges) has no instance for n = 3.
  Part B  every letter relation of Lemma 4.2 (s = lambda_zw, edge e) is derived from Q plus
          literal D_3 / R_3 relators of index <= depth, with O(R) Q-steps; the case split
          (first/second alternative) is complete.

Derivation model (Dehn/van Kampen area).  A state is a word in the free group on the
letters L(x,y) (x != y) and T(x).  Allowed moves, each checked by the VERIFIER:
  * free reduction and cyclic rotation (conjugation): cost 0;
  * 'Q' : replace a subword u by v with |u|+|v| <= 40 and u = v in H_3 (checked on every
          point of depth <= max(|u|,|v|)+3, which pins down both permutations): cost 1;
  * 'CANON': rewrite w into its normal form in the free product of the infinite cyclic
          groups <L(x,y)> (L(y,x) := L(x,y)^-1) and the order-two groups <T(x)>: each
          letter conversion (L(x,y)^-1 -> L(y,x), T^-1 -> T) and each cancellation of
          L(x,y)L(y,x) or T T is a length-2 trivial word, hence a Q relator: cost = number of
          such operations (counted);
  * 'M' : replace a subword u by v where CANON(v u^-1) is a cyclic rotation of CANON(W)
          or of CANON(W)^-1 for a literal family word W built by the verifier from its
          definition in A.1: cost = Area(W) + (CANON cost of W and of v u^-1), the latter
          counted as Q-steps.
A derivation ends at the empty word.  Area(w) <= (#Q-steps) + sum of macro areas.
"""
import itertools, sys

RAYS = (1, 2, 3)
R0 = int(sys.argv[1]) if len(sys.argv) > 1 else 12

# ---------------------------------------------------------------- letters and words
def L(x, y, e=1): return ('L', x, y, e)
def T(x, e=1): return ('T', x, e)

def inv_letter(a):
    return a[:-1] + (-a[-1],)

def inv(w):
    return [inv_letter(a) for a in reversed(w)]

def freereduce(w):
    out = []
    for a in w:
        if out and out[-1] == inv_letter(a):
            out.pop()
        else:
            out.append(a)
    # cyclic reduction (conjugation)
    while len(out) >= 2 and out[0] == inv_letter(out[-1]):
        out = out[1:-1]
    return out

# ---------------------------------------------------------------- permutation evaluation
def act_letter(a, pt):
    r, p = pt
    if a[0] == 'T':
        x, e = a[1], a[2]
        if r == x and p in (1, 2):
            return (x, 3 - p)
        return pt
    _, x, y, e = a
    if e == -1:
        x, y = y, x
    if r == x:
        return (x, p - 1) if p >= 2 else (y, 1)
    if r == y:
        return (y, p + 1)
    return pt

def act(w, pt):
    for a in w:
        pt = act_letter(a, pt)
    return pt

def equal_in_H3(u, v):
    depth = max(len(u), len(v)) + 3
    for r in RAYS:
        for p in range(1, depth + 1):
            if act(u, (r, p)) != act(v, (r, p)):
                return False
    return True

def trivial(w):
    return equal_in_H3(w, [])

# ---------------------------------------------------------------- CANON (free product normal form)
def to_positive(a):
    if a[0] == 'T':
        return ('T', a[1], 1), (1 if a[2] == -1 else 0)
    _, x, y, e = a
    if e == 1:
        return a, 0
    return ('L', y, x, 1), 1

def pos_inverse(a):
    if a[0] == 'T':
        return a
    return ('L', a[2], a[1], 1)

def canon(w):
    """Return (cyclic normal form, number of Q-steps used)."""
    cost = 0
    stack = []
    for a in w:
        b, c = to_positive(a)
        cost += c
        if stack and stack[-1] == pos_inverse(b):
            stack.pop()
            cost += 1
        else:
            stack.append(b)
    while len(stack) >= 2 and stack[0] == pos_inverse(stack[-1]):
        stack = stack[1:-1]
        cost += 1          # conjugation plus one pair cancellation
    return stack, cost

def pos_inv_word(w):
    return [pos_inverse(a) for a in reversed(w)]

def is_rotation(a, b):
    if len(a) != len(b):
        return False
    if not a:
        return True
    n = len(a)
    return any(a[k:] + a[:k] == b for k in range(n))

# ---------------------------------------------------------------- literal words of A.1
def D(x, u, k):
    """D^u_x(k) = lambda_xu^k tau_x lambda_ux^k."""
    return [L(x, u)] * k + [T(x)] + [L(u, x)] * k

class Route:
    def __init__(self, c):
        self.c = c            # dict ray -> route ray
    def Ed_t(self, x, j):
        return D(x, self.c[x], j - 1)
    def Ed_s(self, x, y):
        if x > y:
            x, y = y, x
        return [L(y, x), T(x), L(x, y)]
    def Ed(self, e):
        if e[0] == 't':
            return self.Ed_t(e[1], e[2])
        return self.Ed_s(e[1], e[2])

def comm(U, V):
    return U + V + inv(U) + inv(V)

def family_word(route, fam, p):
    """Literal family word from the table of A.1.  p = tuple of labels/indices."""
    if fam == 'F3':
        x, k = p
        return comm([T(x)], D(x, route.c[x], k))
    if fam == 'R3':
        x, u, v, k = p
        assert len({x, u, v}) == 3
        return D(x, u, k) + inv(D(x, v, k))
    if fam == 'B3':
        x, i, y, j = p
        assert x != y
        return comm(route.Ed_t(x, i), route.Ed_t(y, j))
    if fam == 'C3':
        x, y, z, j = p
        s = (min(x, y), max(x, y))
        assert disjoint(('s',) + s, ('t', z, j))
        return comm(route.Ed_s(x, y), route.Ed_t(z, j))
    if fam == 'D3':
        x, z, w, j = p
        assert len({x, z, w}) == 3
        E = route.Ed_t(x, j)
        return [L(w, z)] + E + [L(z, w)] + inv(E)
    raise ValueError(fam)

# ---------------------------------------------------------------- edges
def verts(e):
    if e[0] == 't':
        return {(e[1], e[2]), (e[1], e[2] + 1)}
    return {(e[1], 1), (e[2], 1)}

def depth(e):
    return max(p for (_, p) in verts(e))

def disjoint(e, f):
    return not (verts(e) & verts(f))

def edges(R):
    out = []
    for x in RAYS:
        for j in range(1, R):
            out.append(('t', x, j))
    for x, y in itertools.combinations(RAYS, 2):
        out.append(('s', x, y))
    return [e for e in out if depth(e) <= R]

def edge_of(pair):
    """The edge with vertex set `pair`, or None."""
    (a, p), (b, q) = sorted(pair)
    if a == b and abs(p - q) == 1:
        return ('t', a, min(p, q))
    if a != b and p == 1 and q == 1:
        return ('s', a, b)
    return None

# ---------------------------------------------------------------- the verifier
class Derivation:
    def __init__(self, route, w, label):
        self.route = route
        self.w = freereduce(list(w))
        self.label = label
        self.q = 0
        self.macros = []
        self.log = []

    def _find(self, u):
        n, m = len(self.w), len(u)
        for i in range(n - m + 1):
            if self.w[i:i + m] == u:
                return i
        return None

    def Q(self, u, v):
        i = self._find(u)
        assert i is not None, (self.label, 'Q: subword not found')
        assert len(u) + len(v) <= 40, (self.label, 'Q: too long')
        assert equal_in_H3(u, v), (self.label, 'Q: not equal in H_3')
        self.w = freereduce(self.w[:i] + list(v) + self.w[i + len(u):])
        self.q += 1

    def canon(self):
        self.w, c = canon(self.w)
        self.q += c

    def M(self, u, v, fam, p):
        i = self._find(u)
        assert i is not None, (self.label, 'M: subword not found', fam, p)
        W = family_word(self.route, fam, p)
        cW, c1 = canon(W)
        r, c2 = canon(list(v) + inv(u))
        ok = is_rotation(r, cW) or is_rotation(r, pos_inv_word(cW))
        assert ok, (self.label, 'M: not a conjugate of the family word', fam, p)
        self.w = freereduce(self.w[:i] + list(v) + self.w[i + len(u):])
        self.q += c1 + c2
        self.macros.append((fam, p))

    def close_by(self, fam, p):
        """The whole (cyclic) word is a conjugate of W^{+-1}: replace it by the empty word."""
        self.M(list(self.w), [], fam, p)

    def finish(self):
        """Close a word that CANON reduces to a trivial word of length <= 40."""
        self.canon()
        if self.w:
            assert len(self.w) <= 40 and trivial(self.w), (self.label, 'finish: residue', len(self.w))
            self.w = []
            self.q += 1
        assert self.w == []
        return self

# ---------------------------------------------------------------- Part A: edge relations
def part_A(route, R):
    stats = {'E1': [], 'E2i': [], 'E2ii': [], 'E2iii/iv': [], 'E2v': [], 'E3': []}
    Es = edges(R)
    for e in Es:
        d = Derivation(route, route.Ed(e) + route.Ed(e), ('E1', e)).finish()
        assert not d.macros
        stats['E1'].append((depth(e), d.q, d.macros))
    for e, f in itertools.product(Es, Es):
        if e == f:
            continue
        Ee, Ef = route.Ed(e), route.Ed(f)
        if disjoint(e, f):
            w = comm(Ee, Ef)
            d = Derivation(route, w, ('E2', e, f))
            R_ = max(depth(e), depth(f))
            if e[0] == 't' and f[0] == 't' and e[1] == f[1]:
                # (E2)(i): conjugation by lambda_{x c}^{i-1} + letter conversions -> F_3(|j-i|)
                x, i, j = e[1], e[2], f[2]
                d.canon()
                d.close_by('F3', (x, abs(j - i)))
                assert abs(j - i) <= R_ - 1
                stats['E2i'].append((R_, d.q, d.macros))
            elif e[0] == 't' and f[0] == 't':
                d.close_by('B3', (e[1], e[2], f[1], f[2]))
                stats['E2ii'].append((R_, d.q, d.macros))
            elif e[0] == 's' and f[0] == 's':
                stats['E2v'].append((e, f))   # must stay empty for n = 3
            else:
                s, t = (e, f) if e[0] == 's' else (f, e)
                d.close_by('C3', (s[1], s[2], t[1], t[2]))
                stats['E2iii/iv'].append((R_, d.q, d.macros))
            assert d.w == []
        elif len(verts(e) & verts(f)) == 1:
            w = Ee + Ef + Ee + inv(Ef + Ee + Ef)
            d = Derivation(route, w, ('E3', e, f)).finish()
            assert not d.macros
            stats['E3'].append((max(depth(e), depth(f)), d.q, d.macros))
    assert stats['E2v'] == [], 'two disjoint top edges exist?'
    return stats

# ---------------------------------------------------------------- Part B: Lemma 4.2
def part_B(route, R):
    stats = {'D3': [], 'free': [], 'reroute': [], 'short': [], 'second': []}
    for z, w_ in itertools.permutations(RAYS, 2):
        s = L(z, w_)
        (x,) = [r for r in RAYS if r not in (z, w_)]
        for e in edges(R):
            img = {act([s], v) for v in verts(e)}
            e2 = edge_of(img)
            if e2 is None:
                # second alternative: e = sigma_{w,y}, y != z
                assert e[0] == 's' and w_ in (e[1], e[2]) and z not in (e[1], e[2]), e
                y = e[1] if e[2] == w_ else e[2]
                assert img == {(w_, 2), (y, 1)}
                t1, sg = route.Ed_t(w_, 1), route.Ed_s(w_, y)
                wd = inv([s]) + route.Ed(e) + [s] + inv(t1 + sg + t1)
                d = Derivation(route, wd, ('L42b', s, e)).finish()
                stats['second'].append((depth(e), d.q, d.macros))
                continue
            wd = inv([s]) + route.Ed(e) + [s] + inv(route.Ed(e2))
            d = Derivation(route, wd, ('L42', s, e))
            if e[0] == 't' and e[1] == x:
                j = e[2]
                assert e2 == e
                d.canon()
                if d.w:
                    d.close_by('D3', (x, z, w_, j))
                stats['D3'].append((depth(e), d.q, d.macros))
            elif e[0] == 't' and e[2] >= 2 and e[1] in (z, w_):
                y, j = e[1], e[2]
                other = w_ if y == z else z          # the route that makes it free
                assert e2 == ('t', y, j - 1 if y == z else j + 1)
                if route.c[y] != other:
                    old = route.c[y]
                    k1 = j - 1                        # Ed(e)  = D^old_y(j-1)
                    k2 = e2[2] - 1                    # Ed(e') = D^old_y(k2)
                    # R_3(0) is the empty relation: D^u_y(0) = D^v_y(0) = tau_y literally
                    if k2 > 0:
                        d.M(inv(D(y, old, k2)), inv(D(y, other, k2)), 'R3', (y, other, old, k2))
                    if k1 > 0:
                        d.M(D(y, old, k1), D(y, other, k1), 'R3', (y, other, old, k1))
                    assert max(k1, k2) <= depth(e)
                    d.finish()
                    stats['reroute'].append((depth(e), d.q, d.macros))
                else:
                    d.finish()
                    stats['free'].append((depth(e), d.q, d.macros))
            else:
                # t_y(1) with y in {z,w}, or a top edge: length <= 40
                assert len(d.w) <= 40
                d.finish()
                stats['short'].append((depth(e), d.q, d.macros))
            assert d.w == [] and depth(e2) <= depth(e) + 1
    return stats

# ---------------------------------------------------------------- main
def summarize(name, rows):
    if not rows:
        return f'  {name:9s}: 0 relations'
    n = len(rows)
    maxq_per_R = max(q / max(R, 1) for (R, q, _) in rows)
    nm = max(len(m) for (_, _, m) in rows)
    fams = sorted({f for (_, _, m) in rows for (f, _) in m})
    return (f'  {name:9s}: {n:5d} relations, max Q-steps/depth = {maxq_per_R:5.2f}, '
            f'max macros per relation = {nm}, families used = {fams}')

def macro_index_ok(rows, slack):
    for (R, _, m) in rows:
        for (f, p) in m:
            if p[-1] > R + slack:
                return False
    return True

def self_test():
    """The verifier must reject wrong steps."""
    route = Route({1: 2, 2: 3, 3: 1})
    bad = 0
    # wrong family index
    try:
        d = Derivation(route, comm(route.Ed_t(1, 2), route.Ed_t(1, 5)), 'neg1')
        d.canon(); d.close_by('F3', (1, 2))
    except AssertionError:
        bad += 1
    # non-trivial Q step
    try:
        d = Derivation(route, [L(1, 2), T(1)], 'neg2'); d.Q([L(1, 2)], [L(1, 3)])
    except AssertionError:
        bad += 1
    # R_3 used for a pair of routes that is not a reroute
    try:
        d = Derivation(route, D(1, 2, 3) + inv(D(1, 3, 4)), 'neg3')
        d.M(D(1, 2, 3), D(1, 3, 4), 'R3', (1, 3, 2, 3))
    except AssertionError:
        bad += 1
    # a Q step whose words agree only on shallow points must be rejected: |u|+|v| > 40
    try:
        d = Derivation(route, [L(1, 2)] * 21 + [L(2, 1)] * 21, 'neg4')
        d.Q([L(1, 2)] * 21 + [L(2, 1)] * 21, [])
    except AssertionError:
        bad += 1
    assert bad == 4, bad
    print('self-test: verifier rejected all 4 invalid steps')

def main():
    self_test()
    total = 0
    worst = {}
    excess = {}
    for choice in itertools.product(*[[r for r in RAYS if r != x] for x in RAYS]):
        c = dict(zip(RAYS, choice))
        route = Route(c)
        A = part_A(route, R0)
        B = part_B(route, R0)
        print(f'route function c = {c}')
        for k, v in list(A.items()) + list(B.items()):
            if k == 'E2v':
                print(f'  {k:9s}: {len(v)} instances (none possible for n = 3)')
                continue
            print(summarize(k, v))
            total += len(v)
            assert macro_index_ok(v, 0), k
            for (R, q, m) in v:
                worst[k] = max(worst.get(k, 0), q / max(R, 1))
                excess[k] = max(excess.get(k, -10**9), q - 8 * R)
            nm = max((len(m) for (_, _, m) in v), default=0)
            assert nm <= (2 if k == 'reroute' else 1), k
    print(f'\nALL CHECKS PASSED: {total} relations derived, depth <= {R0}, 8 route functions.')
    print('Worst Q-steps per unit depth by class:', {k: round(v, 2) for k, v in worst.items()})
    print('max over relations of (Q-steps - 8*depth) by class:', excess)
    assert max(excess.values()) <= 2
    print('=> every relation: Q-steps <= 8R + 2, plus at most one family relator (two R_3 for reroutes).')

if __name__ == '__main__':
    main()
