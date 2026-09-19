"""Fixed-point germs of contracting self-similar groups (w11-101).

For a self-similar group H acting on X^omega, the Roever-Nekrashevych groupoid G_H is the groupoid of germs
of the maps lambda_w h lambda_v^{-1}.  Two of its isomorphism invariants are read off from the finite
"fixing graph" F on a section-closed finite set N of group elements containing the nucleus:

    g --x--> g|_x   whenever g(x) = x.

  * A germ of h in H at a fixed point xi is nontrivial iff every section of h along xi is nontrivial, i.e.
    xi follows an infinite path of F avoiding 1 (eventually inside the nucleus, hence eventually on a cycle).
  * NON-HAUSDORFF: some nontrivial g lies on a cycle of F \ {1} and 1 is reachable from that cycle in F.
    (Then the germs of g and of 1 at the periodic point of the cycle cannot be separated.)
  * TORSION ISOTROPY: some g of finite order > 1 lies on a cycle of F \ {1}; its germ at the periodic point
    is a nontrivial torsion element of an isotropy group.
  * If F \ {1} has no cycle at all, every germ of H at a fixed point is trivial, and the level cocycle
    |w| - |v| embeds every isotropy group of G_H in Z.

Checked groups: Grigorchuk (d=2), basilica IMG(z^2-1) (d=2), Hanoi towers H^(3) (d=3), and as calibration
the adding machine (d=2).  The section-closed set is also used to recompute the nucleus, which must contain the
known nuclei ({1,a,b,c,d}; {1,a^{+-1},b^{+-1},ab^{-1},ba^{-1}}; {1,a,b,c}; {1,a^{+-1}}).
"""
import itertools
import sys

sys.setrecursionlimit(100000)


class Automaton:
    def __init__(self, d, states):
        # states: name -> (perm as tuple image of 0..d-1, list of section names); '1' is the identity
        self.d = d
        self.S = dict(states)
        self.S['1'] = (tuple(range(d)), ['1'] * d)
        for s, (p, secs) in list(states.items()):
            inv = [0] * d
            for x in range(d):
                inv[p[x]] = x
            # s^{-1} at letter y = p(x) has section (s|_x)^{-1}
            self.S[s + "'"] = (tuple(inv), [None] * d)
        for s, (p, secs) in list(states.items()):
            ip, isecs = self.S[s + "'"]
            isecs = list(isecs)
            for x in range(d):
                isecs[p[x]] = self.invname(secs[x])
            self.S[s + "'"] = (ip, isecs)
        self.memo = {}

    @staticmethod
    def invname(s):
        if s == '1':
            return '1'
        return s[:-1] if s.endswith("'") else s + "'"

    def reduce(self, w):
        out = []
        for s in w:
            if s == '1':
                continue
            if out and out[-1] == self.invname(s):
                out.pop()
            else:
                out.append(s)
        return tuple(out)

    def act(self, w, x):
        """Word w acts on the left: w = s_1 ... s_k means s_1(s_2(...(x)))."""
        secs = []
        for s in reversed(w):
            p, sc = self.S[s]
            secs.append(sc[x])
            x = p[x]
        return x, self.reduce(tuple(reversed(secs)))

    def perm(self, w):
        return tuple(self.act(w, x)[0] for x in range(self.d))

    def section(self, w, x):
        return self.act(w, x)[1]

    def trivial(self, w, stack=None):
        w = self.reduce(w)
        if not w:
            return True
        if w in self.memo:
            return self.memo[w]
        stack = set() if stack is None else stack
        if w in stack:
            return True   # greatest fixed point: a cycle of sections with trivial permutations
        if self.perm(w) != tuple(range(self.d)):
            self.memo[w] = False
            return False
        stack.add(w)
        r = all(self.trivial(self.section(w, x), stack) for x in range(self.d))
        stack.discard(w)
        if not stack:
            self.memo[w] = r
        return r

    def inv(self, w):
        return tuple(self.invname(s) for s in reversed(w))

    def equal(self, u, v):
        return self.trivial(u + self.inv(v))

    def order(self, w, cap=64):
        p = ()
        for k in range(1, cap + 1):
            p = p + w
            if self.trivial(p):
                return k
        return None


def closure(A, gens, maxlen=3):
    """Representatives of all words of length <= maxlen in gens and inverses, closed under sections."""
    letters = list(gens) + [g + "'" for g in gens]
    reps = [()]

    def find(w):
        for i, r in enumerate(reps):
            if A.equal(w, r):
                return i
        reps.append(A.reduce(w))
        return len(reps) - 1

    todo = []
    for L in range(1, maxlen + 1):
        for w in itertools.product(letters, repeat=L):
            w = A.reduce(w)
            if len(w) == L:
                n0 = len(reps)
                i = find(w)
                if i == n0:
                    todo.append(i)
    while todo:
        i = todo.pop()
        for x in range(A.d):
            n0 = len(reps)
            j = find(A.section(reps[i], x))
            if j == n0:
                todo.append(j)
    return reps


def analyse(name, A, gens, maxlen):
    reps = closure(A, gens, maxlen)
    idx = {}

    def find(w):
        for i, r in enumerate(reps):
            if A.equal(w, r):
                return i
        raise KeyError(w)

    triv = find(())
    F = {i: [] for i in range(len(reps))}
    for i, w in enumerate(reps):
        p = A.perm(w)
        for x in range(A.d):
            if p[x] == x:
                F[i].append((x, find(A.section(w, x))))
    # full section graph and nucleus = everything reachable from a cycle of the section graph
    Sg = {i: [find(A.section(w, x)) for x in range(A.d)] for i, w in enumerate(reps)}

    def sreach(src):
        seen, st = set(), [src]
        while st:
            v = st.pop()
            for u in Sg[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        return seen
    cyc = [i for i in Sg if i in sreach(i)]
    nucleus = set(cyc)
    for i in cyc:
        nucleus |= sreach(i)
    nontriv = [i for i in F if i != triv]
    # vertices of F \ {1} lying on a cycle
    def reach(src, allowed):
        seen, st = set(), [src]
        while st:
            v = st.pop()
            for _, u in F[v]:
                if u in allowed and u not in seen:
                    seen.add(u)
                    st.append(u)
        return seen
    allowed = set(nontriv)
    oncycle = [i for i in nontriv if i in reach(i, allowed)]
    everything = set(F)
    nonhaus = [i for i in oncycle if triv in reach(i, everything)]
    torsion = [(i, A.order(reps[i])) for i in oncycle]
    torsion = [(i, o) for i, o in torsion if o is not None]
    fmt = lambda i: ''.join(reps[i]) or '1'
    print(f"== {name}: {len(reps)} elements in the section-closed set (words of length <= {maxlen})")
    print(f"   nucleus (sections reachable from cycles of the section graph), {len(nucleus)} elements: {sorted(''.join(reps[i]) or '1' for i in nucleus)}")
    print(f"   nontrivial elements on cycles of the fixing graph: {[fmt(i) for i in oncycle]}")
    for i in oncycle:
        cyc = [(x, fmt(u)) for x, u in F[i] if u in allowed and i in reach(u, allowed) | {u}]
        print(f"      {fmt(i)}: fixed letters -> sections {[(x, fmt(u)) for x, u in F[i]]}")
    print(f"   NON-HAUSDORFF witnesses (cycle element from which 1 is reachable): {[fmt(i) for i in nonhaus]}")
    print(f"   TORSION germs (finite-order cycle elements, order): {[(fmt(i), o) for i, o in torsion]}")
    verdict = []
    if nonhaus:
        verdict.append("groupoid of germs is not Hausdorff")
    if torsion:
        verdict.append("isotropy has torsion")
    if not oncycle:
        verdict.append("all fixed-point germs of H trivial; isotropy of G_H embeds in Z")
    print(f"   VERDICT: {'; '.join(verdict)}")
    return bool(nonhaus), bool(torsion), not oncycle


def main():
    res = {}
    grig = Automaton(2, {'a': ((1, 0), ['1', '1']), 'b': ((0, 1), ['a', 'c']),
                         'c': ((0, 1), ['a', 'd']), 'd': ((0, 1), ['1', 'b'])})
    res['grigorchuk'] = analyse('Grigorchuk group', grig, 'abcd', 2)
    basil = Automaton(2, {'a': ((1, 0), ['1', 'b']), 'b': ((0, 1), ['1', 'a'])})
    res['basilica'] = analyse('basilica group IMG(z^2-1): a = sigma(1,b), b = (1,a)', basil, 'ab', 4)
    hanoi = Automaton(3, {'a': ((1, 0, 2), ['1', '1', 'a']), 'b': ((2, 1, 0), ['1', 'b', '1']),
                          'c': ((0, 2, 1), ['c', '1', '1'])})
    res['hanoi'] = analyse('Hanoi towers group H^(3)', hanoi, 'abc', 2)
    odo = Automaton(2, {'a': ((1, 0), ['1', 'a'])})
    res['adding'] = analyse('adding machine (calibration)', odo, 'a', 3)
    ok = (res['grigorchuk'][:2] == (True, True) and res['hanoi'][1] and not res['hanoi'][0]
          and res['basilica'] == (False, False, True) and res['adding'][2])
    print("EXPECTED PATTERN (Grig: non-Hausdorff+torsion; Hanoi: Hausdorff+torsion; basilica, adding machine: no fixed germs):",
          "OK" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
