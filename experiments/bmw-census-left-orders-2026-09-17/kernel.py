# The kernel Lambda = <A> cap ker(pr_V): horizontal words acting trivially on the vertical tree T_V.
# Exact test on T_V (reduced vertical words): a state is (word, last vertical letter read); the input letters
# at that state are those x with x != iB[last].  w is trivial iff every reachable state acts trivially on
# its first letter.  Prints the reduced horizontal words of length <= L that lie in Lambda.
# usage: kernel.py census.json idx L [V|H]
import sys, itertools, json
from lo_census import load
from irred import letter_maps, act

def trivial(step, inp, inv, w):
    seen = {(w, None)}; todo = [(w, None)]
    while todo:
        u, last = todo.pop()
        for x in range(inp):
            if last is not None and x == inv[last]: continue
            y, u2 = act(step, u, x)
            if y != x: return False
            if (u2, x) not in seen:
                seen.add((u2, x)); todo.append((u2, x))
                if len(seen) > 5_000_000: return None
    return True

if __name__ == "__main__":
    path, want, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    vertical = len(sys.argv) > 4 and sys.argv[4] == 'H'     # 'H': <B> acting on T_H
    G = next(G for i, G in load(path) if i == want)
    nL, inp, step, invL = letter_maps(G, vertical)
    invT = G.iA if vertical else G.iB
    out = []
    for k in range(1, L + 1):
        for w in itertools.product(range(nL), repeat=k):
            if any(invL[w[i]] == w[i + 1] for i in range(k - 1)): continue
            if trivial(step, inp, invT, w): out.append(w)
    print(json.dumps(dict(census=path, idx=want, side='H' if vertical else 'V', L=L, n=len(out), words=out[:200])))
