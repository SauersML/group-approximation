# Irreducibility certificate for a BMW datum: an element g of <A> whose image in Aut(T_B) has infinite order.
# Criterion: if u is a vertex of T_B whose g-orbit has exact length L >= 2 and the section (g^L)|_u equals g or
# g^{-1} as an automorphism of the subtree, then g has infinite order.  (If g had order N, then L | N, and
# ord(g) = ord((g^L)|_u) divides ord(g^L) = N/L, which is impossible.)  An infinite-order element of the stabilizer
# image makes pr_B(Gamma) non-discrete, so Gamma is irreducible: in a reducible lattice pr_B(Gamma) contains the
# discrete group Lambda_2 with finite index.
# usage: irred.py census.json maxlen depth idx...   (horizontal side; add 'V' as the 2nd argument for the vertical)
import sys, json, itertools
from lo_census import load
def letter_maps(G, vertical):
    if not vertical: return G.m, G.n, (lambda a, x: G.SQ[(a, x)]), G.iA
    SQinv = {}
    for (h, v), (v2, h2) in G.SQ.items(): SQinv[(G.iB[v2], h)] = (h2, G.iB[v])
    return G.n, G.m, (lambda a, x: SQinv[(a, x)]), G.iB
def act(step, w, x):
    """word w = (a_1..a_k) acts on input letter x (rightmost letter first); returns (output, section word)."""
    sec = list(w)
    for k in range(len(w) - 1, -1, -1):
        x, sec[k] = step(w[k], x)
    return x, tuple(sec)
def act_path(step, w, u):
    out = []
    for x in u:
        y, w = act(step, w, x); out.append(y)
    return tuple(out), w
def equal(step, inp, w1, w2):
    seen = {(w1, w2)}; todo = [(w1, w2)]
    while todo:
        a, b = todo.pop()
        for x in range(inp):
            (y1, a2), (y2, b2) = act(step, a, x), act(step, b, x)
            if y1 != y2: return False
            if (a2, b2) not in seen:
                seen.add((a2, b2)); todo.append((a2, b2))
                if len(seen) > 2_000_000: return None
    return True
def certificate(G, maxlen, depth, vertical=False):
    L_, inp, step, inv = letter_maps(G, vertical)
    for k in range(1, maxlen + 1):
        for w in itertools.product(range(L_), repeat=k):
            if any(inv[w[i]] == w[i + 1] for i in range(k - 1)) or (k > 1 and inv[w[-1]] == w[0]): continue
            winv = tuple(inv[a] for a in reversed(w))
            for d in range(1, depth + 1):
                for u in itertools.product(range(inp), repeat=d):
                    # exact orbit length of u under g
                    v, L = u, 0
                    while True:
                        v, _ = act_path(step, w, v); L += 1
                        if v == u or L > inp ** d: break
                    if L < 2 or v != u: continue
                    y, sec = act_path(step, w * L, u); assert y == u
                    for tgt, name in ((w, 'g'), (winv, 'g^-1')):
                        if equal(step, inp, sec, tgt):
                            return dict(word=w, vertex=u, orbit=L, section=name)
    return None
if __name__ == "__main__":
    args = sys.argv[1:]; vertical = args[1] == 'V'
    if vertical: del args[1]
    path, maxlen, depth = args[0], int(args[1]), int(args[2]); want = set(map(int, args[3:]))
    for i, G in load(path):
        if i in want:
            print(json.dumps(dict(census=path, idx=i, side='V' if vertical else 'H',
                                  cert=certificate(G, maxlen, depth, vertical))), flush=True)
