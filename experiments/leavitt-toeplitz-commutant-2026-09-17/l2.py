"""Exact arithmetic in the binary Leavitt algebra L = L_{F_2}(1,2).

An element of depth N is a table T: {0,1}^N -> finite F_2-sets of words, meaning
    A delta_{mu z} = sum_{w in T[mu]} delta_{w z}   for every infinite word z.
This is the normal form A = sum_{|mu|=N} R_mu t_mu with R_mu in the free algebra
F_2<s_0,s_1> (s_w delta_z = delta_{wz}, t_mu delta_{mu z} = delta_z).  At a fixed
depth the table is determined by the operator (apply to an aperiodic z), so two
elements are equal iff their tables agree after extension to a common depth.
"""
import itertools, random

def words(n):
    return [''.join(p) for p in itertools.product('01', repeat=n)]

class El:
    __slots__ = ('N', 'T')
    def __init__(self, N, T):
        self.N = N
        self.T = T  # dict prefix -> frozenset

    @staticmethod
    def scalar(c=1):
        return El(0, {'': frozenset({''}) if c else frozenset()})

    @staticmethod
    def s(w):  # s_w
        return El(0, {'': frozenset({w})})

    @staticmethod
    def t(w):  # t_w = s_w^*
        N = len(w)
        return El(N, {m: (frozenset({''}) if m == w else frozenset()) for m in words(N)})

    def extend(self, D):
        if D == self.N:
            return self
        k = D - self.N
        T = {}
        for m, S in self.T.items():
            for v in words(k):
                T[m + v] = frozenset(u + v for u in S)
        return El(D, T)

    def __add__(self, o):
        D = max(self.N, o.N)
        a, b = self.extend(D), o.extend(D)
        return El(D, {m: a.T[m] ^ b.T[m] for m in a.T}).reduce()

    __sub__ = __add__

    def __mul__(self, o):
        # (self*o) delta_{mu z}: first o, then self.
        D = o.N + self.N
        b = o.extend(D)
        NA = self.N
        T = {}
        for m, S in b.T.items():
            acc = set()
            for w in S:
                # |w| >= NA because of the extension
                for u in self.T[w[:NA]]:
                    acc ^= {u + w[NA:]}
            T[m] = frozenset(acc)
        return El(D, T).reduce()

    def reduce(self):
        e = self
        while e.N > 0:
            T2 = {}
            ok = True
            for m in words(e.N - 1):
                S0, S1 = e.T[m + '0'], e.T[m + '1']
                if not all(u.endswith('0') for u in S0) or not all(u.endswith('1') for u in S1):
                    ok = False; break
                A0 = frozenset(u[:-1] for u in S0)
                A1 = frozenset(u[:-1] for u in S1)
                if A0 != A1:
                    ok = False; break
                T2[m] = A0
            if not ok:
                break
            e = El(e.N - 1, T2)
        return e

    def iszero(self):
        return all(not S for S in self.T.values())

    def __eq__(self, o):
        return (self - o).iszero()

    def act(self, vec):
        """vec: set of (long) finite words standing for infinite words."""
        out = set()
        N = self.N
        for w in vec:
            for u in self.T[w[:N]]:
                out ^= {u + w[N:]}
        return out

    def __repr__(self):
        return 'El(N=%d,%s)' % (self.N, {m: sorted(S) for m, S in self.T.items()})

ONE = El.scalar(1)
ZERO = El.scalar(0)
s0, s1, t0, t1 = El.s('0'), El.s('1'), El.t('0'), El.t('1')

def check_relations():
    assert t0 * s0 == ONE and t1 * s1 == ONE
    assert (t0 * s1).iszero() and (t1 * s0).iszero()
    assert s0 * t0 + s1 * t1 == ONE
    return True

if __name__ == '__main__':
    print(check_relations())
