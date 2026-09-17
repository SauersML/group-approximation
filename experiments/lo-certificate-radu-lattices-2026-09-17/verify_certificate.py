"""Independent verifier for a non-left-orderability certificate.

Input: a text file, one triple per line:  p ; q ; r   (words in the a- and b-generators, with ^-1).
It checks, using only the relator strings from bmw.GROUPS (no normal-form code, no pysat):

 1. Every word has even total a-exponent-length and even b-length, so it lies in
    Lambda = ker(Gamma -> Z/2 x Z/2) (a_i -> (1,0), b_j -> (0,1)).
 2. p q r^-1 = 1 in Gamma, by an explicit derivation: every rewriting step replaces a
    subword v u (v a b-letter, u an a-letter) by u' v' only after checking that
    v u v'^-1 u'^-1 is a cyclic rotation of a relator of Gamma or of its inverse.
    Only free reductions and such steps are used, so "reduces to the empty word"
    is a proof of triviality.  (No uniqueness of normal forms is used for soundness:
    words are identified only when the derivation proves them equal.)
 3. No word is trivial, and no key equals the key of its own inverse.
 4. The CNF  P(p) & P(q) => P(r), with P(g^-1) = not P(g), is unsatisfiable, by a
    self-contained DPLL with unit propagation.
"""
import sys

from bmw import GROUPS  # only the relator strings (copied from the arXiv sources) are imported

GROUP = sys.argv[1] if len(sys.argv) > 2 else "incoherent"
NA, NB, REL = GROUPS[GROUP]
KERNEL = (sys.argv[3] if len(sys.argv) > 3 else "kernel") == "kernel"


def letters(s):
    out = []
    for tok in s.split():
        e = -1 if tok.endswith("^-1") else 1
        tok = tok.replace("^-1", "")
        assert tok[0] in "ab" and 1 <= int(tok[1:]) <= (NA if tok[0] == "a" else NB), tok
        out.append((tok[0], e * int(tok[1:])))
    return out


def inv(w):
    return [(t, -x) for (t, x) in reversed(w)]


RELSET = set()
for r in REL:
    w = letters(r)
    for ww in (w, inv(w)):
        for k in range(len(ww)):
            RELSET.add(tuple(ww[k:] + ww[:k]))


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == (x[0], -x[1]):
            out.pop()
        else:
            out.append(x)
    return out


def find_square(v, u):
    """Return (u', v') with v u = u' v', proven by membership of v u v'^-1 u'^-1 in RELSET."""
    hits = []
    for i in range(1, NA + 1):
        for ei in (1, -1):
            for j in range(1, NB + 1):
                for ej in (1, -1):
                    up, vp = ("a", ei * i), ("b", ej * j)
                    if (v, u, ("b", -vp[1]), ("a", -up[1])) in RELSET:
                        hits.append((up, vp))
    assert len(hits) >= 1, ("no square", v, u)
    return hits[0]


SQ = {}


def normal_key(w):
    w = free_reduce(w)
    steps = 0
    while True:
        k = next((i for i in range(len(w) - 1) if w[i][0] == "b" and w[i + 1][0] == "a"), None)
        if k is None:
            break
        key = (w[k], w[k + 1])
        if key not in SQ:
            SQ[key] = find_square(*key)
        up, vp = SQ[key]
        w = free_reduce(w[:k] + [up, vp] + w[k + 2:])
        steps += 1
        assert steps < 10 ** 6
    return tuple(w)


def dpll(clauses, nvars):
    """Complete DPLL: returns True iff satisfiable.  Branches on the most frequent variable."""
    clauses = [tuple(c) for c in clauses]
    occ = {}
    for ci, c in enumerate(clauses):
        for l in c:
            occ.setdefault(l, []).append(ci)
    freq = sorted(range(1, nvars + 1), key=lambda v: -(len(occ.get(v, ())) + len(occ.get(-v, ()))))
    sys.setrecursionlimit(100000)
    nodes = [0]

    def closure(assumptions):
        """Unit propagation; None on conflict, else the set of implied literals."""
        val = set()
        for l in assumptions:
            if -l in val:
                return None
            val.add(l)
        queue = []
        pending = range(len(clauses))
        while True:
            for ci in pending:
                c = clauses[ci]
                if any(l in val for l in c):
                    continue
                unk = [l for l in c if -l not in val]
                if not unk:
                    return None
                if len(unk) == 1:
                    val.add(unk[0])
                    queue.append(unk[0])
            if not queue:
                return val
            pend = set()
            while queue:
                pend.update(occ.get(-queue.pop(), ()))
            pending = sorted(pend)

    def solve(assumptions):
        nodes[0] += 1
        val = closure(assumptions)
        if val is None:
            return False
        free = next((v for v in freq if v not in val and -v not in val), None)
        if free is None:
            return True
        return solve(assumptions + [free]) or solve(assumptions + [-free])

    res = solve([])
    print("DPLL nodes:", nodes[0])
    return res


def main(path):
    triples = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        p, q, r = [letters(x) for x in line.split(";")]
        triples.append((p, q, r))
    keys = {}
    var = {}
    nv = 0

    def lit(w):
        nonlocal nv
        a = sum(1 for t, _ in w if t == "a")
        b = sum(1 for t, _ in w if t == "b")
        assert (not KERNEL) or (a % 2 == 0 and b % 2 == 0), ("not in kernel", w)
        k = normal_key(w)
        assert k != (), ("trivial element", w)
        if k in var:
            return var[k]
        ki = normal_key(inv(w))
        assert ki != k, ("element equal to its inverse", w)
        if ki in var:
            # w is proven to be the inverse of an element already named
            var[k] = -var[ki]
            return var[k]
        nv += 1
        var[k] = nv
        var[ki] = -nv
        return nv

    clauses = []
    for p, q, r in triples:
        assert normal_key(p + q + inv(r)) == (), ("triple not a product", p, q, r)
        clauses.append((-lit(p), -lit(q), lit(r)))
    print("triples verified:", len(triples), "variables:", nv)
    sat = dpll(clauses, nv)
    print("CNF satisfiable:", sat)
    print("CERTIFICATE VALID" if not sat else "certificate INVALID")


if __name__ == "__main__":
    # usage: verify_certificate.py GROUP CERTFILE {kernel|full}
    main(sys.argv[2])
