#!/usr/bin/env python3
"""Cyclic-coset collision test for the 195 surviving binary four-address rule classes.

Lemma (coset collision).  Let tau(x)(g) = mu((x(g m_i))_i), U <= G a subgroup, and let
pi_U be the partition of {0,1,2,3} with i ~ j iff m_i U = m_j U (iff m_i^-1 m_j in U).
The pattern of x = 1_U at g has bit i equal to [g m_i in U] = [g in U m_i^-1], and
U m_i^-1 = U m_j^-1 iff i ~ j.  So every pattern of 1_U is 0000 or 1_C for a block C.
  (A) mu(1_C) = mu(0000) for every block C  =>  tau(1_U) = tau(0), and 1_U != 0.
  (B) mu(1 - 1_C) = mu(1111) for every block C  =>  tau(1 - 1_U) = tau(1).
Either way tau is not injective.

Use U = <q> with q = m_i^-1 m_j.  In a group realizing a coarsening of the quotient
partition P, pi_U contains i ~ j and k ~ l for every ordered pair (k,l) whose quotient is
q or q^-1 in P (closed under transitivity).  The adversary may coarsen further.  If pi_U is
the one-block partition then M is inside U, so <M> is cyclic, hence amenable, and an injective
tau is balanced (Gromov--Weiss).  So a blocking partition P is *killed* when some pair (i,j)
makes (A) or (B) hold on every non-full coarsening of its forced partition.

A survivor rule is excluded over every group when every one of its blocking partitions
(analyze3.json 'survivors') is killed: a group realizing a coarsening Q of a minimal failing
partition either has amenable memory (excluded by the census) or Q coarsens a blocking P.

Mode "flip" (optional 4th argument) also accepts, on a coarsening pi, a single flip at h in U
on the background 1_U (or 1 - 1_U): it is invisible iff mu(1_C(i)) = mu(1_C(i) - e_i) for every i
(resp. the complement), giving tau(1_U) = tau(1_U + delta_h), a finite-support collision.

Usage: coset.py ../gottschalk-four-address-balance/flip1.json ../gottschalk-four-address-balance/analyze3.json \
                ../gottschalk-four-address-balance/dflip3.json [collision|flip]
"""
import itertools, json, sys

PAIRS = [(i, j) for i in range(4) for j in range(4) if i != j]
PIDX = {p: k for k, p in enumerate(PAIRS)}


def ev(mu, bits):
    x = bits[0] | (bits[1] << 1) | (bits[2] << 2) | (bits[3] << 3)
    return (mu >> x) & 1


def ind(block):
    return [1 if i in block else 0 for i in range(4)]


def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        for k in range(len(p)):
            yield p[:k] + [[first] + p[k]] + p[k + 1:]
        yield [[first]] + p


ALL4 = list(set_partitions([0, 1, 2, 3]))


def coarsens(pi, forced):
    """pi coarsens forced iff every forced block lies inside one block of pi."""
    blk = {}
    for b, block in enumerate(pi):
        for i in block:
            blk[i] = b
    return all(len({blk[i] for i in fb}) == 1 for fb in forced)


MODE = "collision"


def good(mu, pi):
    z, o = ev(mu, [0] * 4), ev(mu, [1] * 4)
    a = all(ev(mu, ind(C)) == z for C in pi)
    b = all(ev(mu, [1 - t for t in ind(C)]) == o for C in pi)
    if a or b or MODE == "collision":
        return a or b
    # MODE "flip": flip one site h in U on the background 1_U (resp. 1 - 1_U).  The reader
    # h m_i^-1 sees the background pattern 1_{C(i)} (resp. its complement) with coordinate i
    # toggled, so the flip is invisible iff the rule is blind in coordinate i there, for all i.
    c = all(ev(mu, ind(C)) == ev(mu, [t if k != i else 0 for k, t in enumerate(ind(C))])
            for C in pi for i in C)
    d = all(ev(mu, [1 - t for t in ind(C)]) ==
            ev(mu, [1 - t if k != i else 1 for k, t in enumerate(ind(C))])
            for C in pi for i in C)
    return c or d


def forced_partition(lbl, i, j):
    parent = list(range(4))

    def f(x):
        while parent[x] != x:
            x = parent[x]
        return x

    def u(x, y):
        parent[f(x)] = f(y)

    cls = {lbl[PIDX[(i, j)]], lbl[PIDX[(j, i)]]}
    for (k, l) in PAIRS:
        if lbl[PIDX[(k, l)]] in cls:
            u(k, l)
    groups = {}
    for x in range(4):
        groups.setdefault(f(x), []).append(x)
    return list(groups.values())


def kill_pair(mu, lbl):
    """Return a killing pair (i, j) for this blocking partition, or None."""
    for i, j in itertools.combinations(range(4), 2):
        forced = forced_partition(lbl, i, j)
        ok = True
        for pi in ALL4:
            if len(pi) == 1 or not coarsens(pi, forced):
                continue
            if not good(mu, pi):
                ok = False
                break
        if ok:
            return (i, j)
    return None


def main():
    global MODE
    if len(sys.argv) > 4:
        MODE = sys.argv[4]
    flip1 = json.load(open(sys.argv[1]))
    an = json.load(open(sys.argv[2]))
    dfl = json.load(open(sys.argv[3]))
    parts = flip1["partitions"]
    closed_df = set(dfl["closed"])
    surv = an["survivors"]
    killed, kept = {}, {}
    for r, blocks in sorted(surv.items(), key=lambda t: int(t[0])):
        mu = int(r)
        wit = {}
        for P in blocks:
            wit[P] = kill_pair(mu, parts[P])
        if all(w is not None for w in wit.values()):
            killed[mu] = {str(P): list(w) for P, w in wit.items()}
        else:
            kept[mu] = [P for P, w in wit.items() if w is None]
    open_df = [int(r) for r in surv if int(r) not in closed_df]
    out = {
        "survivors": len(surv),
        "killed_by_coset": len(killed),
        "still_open_after_coset": len(kept),
        "dflip3_open": len(open_df),
        "dflip3_open_killed_by_coset": sum(1 for r in open_df if r in killed),
        "open_after_coset_and_dflip3": sorted(r for r in kept if r not in closed_df),
        "killed": killed,
        "kept_blocking": kept,
    }
    json.dump(out, sys.stdout, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()
