"""Arithmetic of the nine-copy theorem for Rips-Segev two-layer relations (lane w15-060).

Model (proved in rips-segev-nine-copy-no-zero-divisors-proof):
* a face of syllable length l (even, l >= 42) has at most l - 42 single b-syllables (girth of Phi);
* a shell with i interior arcs has an exterior arc of at least floor((8 - i) l / 8) + 1 syllables;
* a window with n* b-syllables (partial ends included), e* whole b^2-syllables and E* = n* + e* <= 39 b-edges
  is contradictory for N copies when n* + max(0, e* - N) >= 2N (eight-copy proof, Lemma 3).
The adversary chooses the arc: which end types (a or b), and which whole b-syllables are singles (at most
l - 42 of them).  A partial end b-syllable carries one b-edge and is not a whole double.

Checks:
 (1) every shell with i <= 2 contains a contradictory window at N = 9, for every l >= 42;
 (2) every shell with i = 3 and l >= 56 contains one;
 (3) a shell with i = 3 and 42 <= l <= 54 carries at least beta(l) >= 21 b-edges on its exterior arc;
 (4) 6 * min beta = 126 > 117 = N + 3 N (N - 1) / 2 at N = 9.
"""

def arc_len(l, i):
    return ((8 - i) * l) // 8 + 1

def window_shapes(m):
    """Syllable windows of length m: (n_b, n_whole_b, partial_b) for a-start and b-start."""
    out = []
    for bstart in (False, True):
        types = [((k % 2 == 0) == bstart) for k in range(m)]  # True = b-syllable
        nb = sum(types)
        partial = int(types[0]) + int(types[-1])
        out.append((nb, nb - partial, partial))
    return out

def worst_window(l, m, N):
    """Min over adversaries of max over windows (of length <= m, inside an arc of m syllables) of the
    Lemma-3 quantity, restricted to windows with E* <= 39.  Returns True if every adversary loses."""
    t1 = l - 42
    # the adversary fixes the arc; we may pick any sub-window.  Conservative: we only use windows that
    # are initial segments of the arc of length m' <= m, and the adversary places singles in the window.
    for bstart in (False, True):
        for singles in range(0, t1 + 1):
            ok = False
            for mp in range(1, m + 1):
                # window = first mp syllables of the arc; its first syllable type is that of the arc
                types = [((k % 2 == 0) == bstart) for k in range(mp)]
                nb = sum(types)
                partial = int(types[0]) + (int(types[-1]) if mp > 1 else 0)
                whole = nb - partial
                s = min(singles, whole)
                e = whole - s
                E = nb + e
                if E <= 39 and nb + max(0, e - N) >= 2 * N:
                    ok = True; break
            if not ok:
                return False
    return True

def beta(l):
    """Min number of b-edges on an exterior arc of >= sigma(l) syllables of a face of length l."""
    m = arc_len(l, 3)
    best = None
    for nb, whole, partial in window_shapes(m):
        e = max(0, whole - (l - 42))
        val = nb + e
        best = val if best is None else min(best, val)
    return best

if __name__ == '__main__':
    N = 9
    A = N + 3 * N * (N - 1) // 2
    for i in (0, 1, 2):
        for l in range(42, 201, 2):
            m = arc_len(l, i) if i else l
            assert worst_window(l, m, N), (i, l)
    print("(1) every shell with i <= 2 closes at N = 9 for 42 <= l <= 200 (and trivially beyond: >= 36 syllables)")
    for l in range(56, 201, 2):
        assert worst_window(l, arc_len(l, 3), N), l
    print("(2) every shell with i = 3 and l >= 56 closes at N = 9 (checked to 200; sigma >= 36 beyond)")
    for l in range(42, 56, 2):
        print(f"    l = {l}: sigma = {arc_len(l, 3)}, i=3 window closes: {worst_window(l, arc_len(l, 3), N)}, beta = {beta(l)}")
    mb = min(beta(l) for l in range(42, 56, 2))
    print(f"(3) min beta over 42..54 = {mb}")
    print(f"(4) 6 * {mb} = {6 * mb} > A(9) = {A}: {6 * mb > A}")
    for N2 in range(9, 13):
        print(f"    A({N2}) = {N2 + 3 * N2 * (N2 - 1) // 2}")
