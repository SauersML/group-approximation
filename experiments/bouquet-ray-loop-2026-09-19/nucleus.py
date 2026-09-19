#!/usr/bin/env python3
"""Exact contraction certificates for self-similar groups given by unit-weight recursions.

Certificate (Lemma N of `linear-bouquet-recursions-ray-loop-and-contraction-proof`): a finite set
N of group elements, closed under sections, together with a finite section-closed set Y
containing the generators, such that for every n in N u {1} and y in Y the section graph of n*y
is finite and every vertex lying on a cycle of it belongs to N.  Then every g in G has all
sections in N below some level, so G is contracting with nucleus inside N.

Elements are reduced words; two words are identified only after an exact check: equal level-L
fingerprints and R.trivial(u v^-1) (a finite section-closed set of words with trivial root
permutations).  Different fingerprints prove the elements distinct.
"""
import hashlib
import numpy as np
from loopgraph import N as NX, ID, reduce, inv
from bouquets import Levels

class Elements:
    def __init__(self, R, L=3, cap=60000):
        self.R, self.L, self.cap = R, L, cap
        self.lv = Levels(R, L)
        self.buckets = {}      # fingerprint -> list of element ids
        self.words = []        # id -> representative word
        self.sec = []          # id -> tuple of section ids (filled lazily)
        self.perm = []
    def fp(self, w):
        return hashlib.blake2b(self.lv.word(w, self.L).astype(np.int32).tobytes(), digest_size=16).digest()
    def ident(self, w):
        """id of the element represented by w, creating it if new"""
        w = reduce(w); f = self.fp(w)
        for i in self.buckets.get(f, []):
            u = self.words[i]
            if u == w or self.R.trivial(w + inv(u)): return i
        i = len(self.words)
        if i >= self.cap: raise OverflowError("element cap")
        self.words.append(w); self.sec.append(None); self.perm.append(self.R.perm(w))
        self.buckets.setdefault(f, []).append(i)
        return i
    def sections(self, i):
        if self.sec[i] is None:
            self.sec[i] = tuple(self.ident(self.R.sec(self.words[i], x)) for x in range(NX))
        return self.sec[i]
    def closure(self, ids, cap=None):
        seen, todo = set(), list(ids)
        while todo:
            i = todo.pop()
            if i in seen: continue
            seen.add(i)
            if cap and len(seen) > cap: raise OverflowError("section graph cap")
            todo.extend(self.sections(i))
        return seen
    def cycle_vertices(self, ids):
        """vertices of the section graph (on the closure of ids) that lie on a directed cycle"""
        V = self.closure(ids)
        idx, low, st, on, out, c = {}, {}, [], set(), set(), [0]
        for r in V:
            if r in idx: continue
            stack = [(r, iter(self.sections(r)))]; idx[r] = low[r] = c[0]; c[0] += 1; st.append(r); on.add(r)
            while stack:
                v, it = stack[-1]
                nxt = next(it, None)
                if nxt is not None:
                    if nxt not in idx:
                        idx[nxt] = low[nxt] = c[0]; c[0] += 1; st.append(nxt); on.add(nxt)
                        stack.append((nxt, iter(self.sections(nxt))))
                    elif nxt in on: low[v] = min(low[v], idx[nxt])
                    continue
                stack.pop()
                if stack: low[stack[-1][0]] = min(low[stack[-1][0]], low[v])
                if low[v] == idx[v]:
                    comp = []
                    while True:
                        u = st.pop(); on.discard(u); comp.append(u)
                        if u == v: break
                    if len(comp) > 1 or v in self.sections(v): out.update(comp)
        return out

def contraction_certificate(R, gens, L=3, cap=60000, log=None):
    """returns (E, N, Y) with N the certified nucleus superset (ids), or raises OverflowError"""
    E = Elements(R, L, cap)
    one = E.ident(())
    Y = E.closure([E.ident(((g, 1),)) for g in gens] + [E.ident(((g, -1),)) for g in gens])
    Nset = set(E.cycle_vertices(Y)) | {one}
    Nset = E.closure(Nset)
    todo, done = sorted(Nset), 0
    while todo:
        n = todo.pop(); done += 1
        for y in sorted(Y):
            p = E.ident(E.words[n] + E.words[y])
            new = [c for c in E.cycle_vertices([p]) if c not in Nset]
            if new:
                add = E.closure(new) - Nset
                Nset |= add; todo.extend(sorted(add))
        if log and done % 500 == 0: log(f"  checked {done}, |N| = {len(Nset)}, elements {len(E.words)}")
    return E, Nset, Y
