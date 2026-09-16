#!/usr/bin/env python3
"""Exact Tietze simplification of finite presentations.

Every move is a Tietze transformation, so the output presents a group isomorphic
to the input:
  * free and cyclic reduction of relators, deletion of empty relators and of
    duplicates up to cyclic permutation and inversion;
  * elimination of a generator occurring exactly once in some relator: that
    relator expresses it as a word in the other generators, which is substituted
    into every other relator, and the relator and generator are deleted.
"""


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def cyc_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def inv(w):
    return tuple(-x for x in reversed(w))


def canon(w):
    """Canonical representative of w up to cyclic permutation and inversion."""
    w = cyc_reduce(w)
    if not w:
        return w
    cands = []
    for u in (w, inv(w)):
        for i in range(len(u)):
            cands.append(u[i:] + u[:i])
    return min(cands, key=lambda c: (sum(1 for x in c if x < 0), c))


def normalize(rels):
    seen = set()
    out = []
    for r in rels:
        c = canon(r)
        if c and c not in seen:
            seen.add(c)
            out.append(c)
    return out


def substitute(w, g, repl):
    """Replace generator g (positive int) by word repl in w."""
    out = []
    rinv = inv(repl)
    for x in w:
        if x == g:
            out.extend(repl)
        elif x == -g:
            out.extend(rinv)
        else:
            out.append(x)
    return free_reduce(tuple(out))


def total_len(rels):
    return sum(len(r) for r in rels)


def nielsen_improve(gens, rels, log=None):
    """Apply one Nielsen move x -> x y^e or x -> y^e x (an automorphism of the free
    group on gens) that strictly lowers the total cyclically reduced relator length.
    Returns (rels, True) if a move was applied."""
    base = total_len(rels)
    best = None
    for x in gens:
        for y in gens:
            if x == y:
                continue
            for e in (1, -1):
                for side in ("R", "L"):
                    repl = (x, e * y) if side == "R" else (e * y, x)
                    new = normalize([substitute(r, x, repl) for r in rels])
                    t = total_len(new)
                    if t < base and (best is None or t < best[0]):
                        best = (t, new, (x, repl))
    if best is None:
        return rels, False
    if log is not None:
        log.append(("nielsen",) + best[2])
    return best[1], True


def reduce_mod_invol(w, invol):
    """Rewrite w modulo x^2 = 1 for x in invol: x^-1 -> x, then cancel xx and
    x x^-1 pairs, cyclically.  The result equals a conjugate of w in any group in
    which every x in invol is an involution."""
    w = tuple(abs(x) if (x < 0 and -x in invol) else x for x in w)

    def cancels(p, q):
        return p == -q or (p == q and p in invol)

    out = []
    for y in w:
        if out and cancels(out[-1], y):
            out.pop()
        else:
            out.append(y)
    while len(out) >= 2 and cancels(out[-1], out[0]):
        out = out[1:-1]
    return tuple(out)


def involution_substitute(gens, rels, log=None):
    """If x^2 is a relator, replace every x^-1 by x in the other relators.  Since
    x^-1 = x in the group, each new relator equals the old one there, so the normal
    closure is unchanged (a composite of Tietze moves).  Returns (rels, changed)."""
    invol = {abs(r[0]) for r in rels if len(r) == 2 and r[0] == r[1]}
    out = []
    for r in rels:
        if len(r) == 2 and r[0] == r[1] and abs(r[0]) in invol:
            out.append(r)
            continue
        out.append(reduce_mod_invol(r, invol))
    old = set(normalize(rels))
    rels = normalize(out)
    # progress measure: strictly fewer inverse letters of involutions, or a
    # strictly shorter total length after free reduction
    def inv_letters(rs):
        return sum(1 for r in rs for x in r if x < 0 and -x in invol and len(r) > 2)
    changed = set(rels) != old and (total_len(rels) < total_len(old) or
                                    inv_letters(rels) < inv_letters(old))
    if changed and log is not None:
        log.append(("involution", sorted(invol)))
    return rels, changed


def simplify(gens, rels, log=None):
    """Alternate generator elimination, involution substitution and
    length-reducing Nielsen moves until none applies."""
    gens, rels = eliminate(gens, rels, log)
    while True:
        rels2, ok = involution_substitute(gens, rels, log)
        if ok:
            gens, rels = eliminate(gens, rels2, log)
            continue
        rels2, ok = nielsen_improve(gens, rels, log)
        if not ok:
            return gens, rels
        gens, rels = eliminate(gens, rels2, log)


def eliminate(gens, rels, log=None):
    """gens: list of positive ints; rels: list of words. Returns (gens, rels)."""
    gens = list(gens)
    rels = normalize(rels)
    changed = True
    while changed:
        changed = False
        for r in sorted(rels, key=len):
            counts = {}
            for x in r:
                counts[abs(x)] = counts.get(abs(x), 0) + 1
            singles = [g for g, c in counts.items() if c == 1]
            if not singles:
                continue
            g = min(singles)
            i = [abs(x) for x in r].index(g)
            # r = u g^e v = 1  =>  g^e = u^-1 v^-1  (up to cyclic rotation v u g^e = 1)
            rot = r[i + 1:] + r[:i]          # rot * g^e ... cyclic: g^e rot = 1
            e = r[i]
            # g^e * rot = 1  => g^e = rot^-1
            val = inv(rot)
            if e < 0:
                val = inv(val)
            others = [x for x in rels if x is not r]
            rels = normalize([substitute(x, g, val) for x in others])
            gens.remove(g)
            if log is not None:
                log.append((g, val))
            changed = True
            break
    return gens, rels
