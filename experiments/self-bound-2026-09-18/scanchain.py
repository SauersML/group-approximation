"""All H(2) square-tiled surfaces with at most N squares (both horizontal cylinder diagrams): least
excess-lowering chain of at most two swaps (chain2: first swap neutral, second a slit pair from the cone
point; or a single lowering swap), with a 1x1 flat padding torus.  Prints the worst cases."""
import sys, subprocess
from h2 import onecyl, twocyl
from swap import tori, excess, Surf
def chain(B, C, L1, L2, pad=(1, 1)):
    tb, tc = tori([pad]); d = len(B)
    B = B + [d + y for y in tb]; C = C + [d + y for y in tc]
    inp = f"{len(B)}\n" + " ".join(map(str, B)) + "\n" + " ".join(map(str, C)) + "\n"
    out = subprocess.run(['./chain2', str(L1), str(L2)], input=inp, capture_output=True, text=True).stdout
    l0 = int(out.split('length')[1].split()[0])
    t = out.split('total')[1].split()[0] if 'total' in out else None
    tot = int(t) if t else None
    cands = [x for x in (l0 or None, tot) if x]
    return min(cands) if cands else None
def surfaces(N):
    for n in range(3, N+1):
        for a in range(1, n-1):
            for b in range(1, n-a):
                for H in range(1, N//n + 1):
                    for tw in range(n): yield 'one', (a, b, n-a-b, H, tw)
    for w1 in range(1, N):
        for l in range(1, N):
            for h1 in range(1, N):
                for h2 in range(1, N):
                    if w1*h1 + (w1+l)*h2 > N: continue
                    for t1 in range(w1):
                        for t2 in range(w1+l): yield 'two', (w1, h1, t1, l, h2, t2)
if __name__ == '__main__':
    N, L1, L2 = map(int, sys.argv[1:4]); res = []; cnt = 0
    for kind, args in surfaces(N):
        B, C = (onecyl if kind == 'one' else twocyl)(*args)
        if excess(B, C) != 2 or len(Surf(B, C).cones()) != 1: continue
        cnt += 1; res.append((chain(B, C, L1, L2) or 99, kind, args))
    res.sort(reverse=True); print('surfaces', cnt)
    import collections; print('hist', sorted(collections.Counter(r[0] for r in res).items()))
    for r in res[:15]: print(r)
