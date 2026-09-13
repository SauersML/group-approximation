#!/usr/bin/env python3
"""Explicit automorphisms of F(h2,h3) carrying A--T C5 relators (73), (77)
to torus-knot relators, found by breadth-first search over Nielsen and
Whitehead moves, then re-verified by direct substitution."""
from collections import deque
from cycle_relators import cred, inv, NIELSEN, apply_aut, syllables

def compose(phi, psi):
    """(phi o psi): first psi, then phi, as images of generators."""
    return {g: apply_aut_word(psi[g], phi) for g in (1, 2)}

def apply_aut_word(w, phi):
    out = []
    for c in w:
        img = phi[abs(c)]
        out.extend(img if c > 0 else inv(img))
    return red(out)

def red(w):
    out = []
    for c in w:
        if out and out[-1] == -c:
            out.pop()
        else:
            out.append(c)
    return out

def cyc_min(w):
    w = cred(w)
    best = None
    for u in (w, inv(w)):
        for s in range(len(u)):
            t = tuple(u[s:] + u[:s])
            best = t if best is None or t < best else best
    return best

def search(r, slack=4, cap=200000):
    ident = {1: [1], 2: [2]}
    start = cyc_min(r)
    seen = {start: ident}
    q = deque([start])
    while q and len(seen) < cap:
        u = q.popleft()
        phi_u = seen[u]
        syl = syllables(list(u))
        if len(syl) == 2 and abs(syl[0][1]) >= 2 and abs(syl[1][1]) >= 2:
            return u, phi_u
        for psi in NIELSEN:
            v = cyc_min(apply_aut(list(u), psi))
            if len(v) <= len(start) + slack and v not in seen:
                seen[v] = compose(psi, phi_u)
                q.append(v)
    return None, None

def show(w):
    return " ".join(("h2" if abs(c) == 1 else "h3") + ("" if c > 0 else "^-1") for c in w)

r73 = [1, -2, -2, 1, 1, -2, 1]       # h2 h3^-2 h2^2 h3^-1 h2
r77 = [1, -2, -2, 1, -2, -2, 1]      # (h2 h3^-2)^2 h2
at_tietze_73 = [1, -2, -1, -2, -2]   # A-T's claimed transform h2 h3^-1 h2^-1 h3^-2
for name, r in (("73", r73), ("77", r77)):
    u, phi = search(r)
    img = cred(apply_aut_word(r, phi))
    ok = u is not None and cyc_min(img) == u
    print("relator (%s) %s" % (name, show(r)))
    print("   phi(h2) = %s ; phi(h3) = %s" % (show(phi[1]), show(phi[2])))
    print("   phi(r) cyclically = %s  syllables %s  verified %s" % (show(img), syllables(list(u)), ok))
# A--T's Tietze step h3 -> h2 h3 on (73)
t = cred(apply_aut_word(r73, {1: [1], 2: [1, 2]}))
print("h3 -> h2 h3 applied to (73):", show(t), "| A-T wrote:", show(at_tietze_73),
      "| equal up to cyclic/inverse:", cyc_min(t) == cyc_min(at_tietze_73))
t2 = cred(apply_aut_word(r73, {1: [1], 2: [2, 1]}))
print("h3 -> h3 h2 applied to (73):", show(t2))
