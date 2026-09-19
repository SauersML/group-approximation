"""H(2) square-tiled surfaces (genus 2, one 6pi cone point) from horizontal cylinder diagrams."""
from swap import excess, Surf, profile
def onecyl(a, b, c, H, tw=0):
    """one cylinder, circumference n=a+b+c, height H; top intervals (A,B,C) glued to bottom order (C,B,A),
    with twist tw."""
    L = [a, b, c]; n = a + b + c; d = n*H
    bb = [j*n + (i+1) % n for j in range(H) for i in range(n)]
    cc = [0]*d
    for j in range(H-1):
        for i in range(n): cc[j*n+i] = (j+1)*n + i
    st = [0, a, a+b]; bot = {}; pos = 0
    for k in (2, 1, 0):
        bot[k] = pos; pos += L[k]
    for k in range(3):
        for u in range(L[k]):
            cc[(H-1)*n + st[k] + u] = (bot[k] + u + tw) % n
    return bb, cc
def twocyl(w1, h1, t1, l, h2, t2):
    """C1: circumference w1, height h1 (rows 0..h1-1); C2: circumference w2 = w1 + l, height h2.
    Top of C1 glued to bottom of C2 on [0, w1) (twist t1); top of C2 = [0,w1) -> bottom of C1 (twist t2 mod),
    and [w1, w2) of C2's top -> [w1, w2) of C2's bottom (the short saddle connection s3)."""
    w2 = w1 + l; d = w1*h1 + w2*h2
    def s1(i, j): return j*w1 + i % w1
    def s2(i, j): return w1*h1 + j*w2 + i % w2
    bb = [0]*d; cc = [0]*d
    for j in range(h1):
        for i in range(w1):
            bb[s1(i, j)] = s1(i+1, j)
            cc[s1(i, j)] = s1(i, j+1) if j < h1-1 else s2((i + t1) % w1, 0)
    for j in range(h2):
        for i in range(w2):
            bb[s2(i, j)] = s2(i+1, j)
            if j < h2-1: cc[s2(i, j)] = s2(i, j+1)
    # top of C2: positions p = (i + t2) mod w2; p in [0,w1) -> C1 bottom p, else -> C2 bottom p
    for i in range(w2):
        p = (i + t2) % w2
        cc[s2(i, h2-1)] = s1(p, 0) if p < w1 else s2(p, 0)
    return bb, cc
if __name__ == '__main__':
    import sys
    for args in [(1,3,3,6),(1,5,5,10),(1,8,8,16),(2,5,7,12)]:
        b, c = onecyl(*args); S = Surf(b, c)
        print('one', args, excess(b, c), [len(S.cls[v]) for v in S.cones()], profile(b, c, 14))
    for args in [(5,1,0,1,4,0),(6,6,0,1,6,0),(10,10,0,1,10,0),(10,10,3,1,10,2)]:
        b, c = twocyl(*args); S = Surf(b, c)
        print('two', args, excess(b, c), [len(S.cls[v]) for v in S.cones()], profile(b, c, 14))
