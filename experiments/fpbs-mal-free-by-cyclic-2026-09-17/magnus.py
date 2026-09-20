"""Magnus rewriting of r for characters psi of M = <b,t | r>.

For psi(b) = 1, psi(t) = k substitute t = y b^k (psi(y) = 0) and write r in
y_i = b^i y b^-i.  Then ker psi = <y_i | r_i (i in Z)> with r_i the i-shift.
If the maximal index m+ and the minimal index m- among the y-letters of r
each occur exactly once, Tietze moves eliminate every y_i outside
[m-, m+ - 1] and ker psi is free of rank m+ - m-.  The script prints the
rewritten relator, the multiplicities of the extreme indices and the rank,
next to the Alexander width prediction n = width + 1 with
width(psi) = max(0, 2 psi(b), psi(t)) - min(0, 2 psi(b), psi(t)).
For psi(b) = 0 (psi = psi_0, kernel Gamma_mal) it rewrites in b_i = t^i b t^-i.
"""
from fox import WORD


def rewrite_b_direction(k):
    """psi(b)=1, psi(t)=k; letters y (index = current height) and powers of b."""
    out, h = [], 0
    for g, e in WORD:
        if g == 'b':
            h += e
        else:
            if e == 1:          # t = y b^k : letter y at height h, then b^k
                out.append((h, 1))
                h += k
            else:               # t^-1 = b^-k y^-1
                h -= k
                out.append((h, -1))
    assert h == 0
    return out


def rewrite_t_direction():
    """psi(b)=0, psi(t)=1 : letters b at height h."""
    out, h = [], 0
    for g, e in WORD:
        if g == 't':
            h += e
        else:
            out.append((h, e))
    assert h == 0
    return out


def free_reduce(w):
    st = []
    for x in w:
        if st and st[-1][0] == x[0] and st[-1][1] == -x[1]:
            st.pop()
        else:
            st.append(x)
    while len(st) > 1 and st[0][0] == st[-1][0] and st[0][1] == -st[-1][1]:
        st = st[1:-1]
    return st


def summary(w):
    w = free_reduce(w)
    idx = [i for i, _ in w]
    hi, lo = max(idx), min(idx)
    return w, hi, idx.count(hi), lo, idx.count(lo)


def width(be, ta):
    v = [0, 2 * be, ta]
    return max(v) - min(v)


if __name__ == '__main__':
    for k in range(-5, 7):
        w, hi, chi, lo, clo = summary(rewrite_b_direction(k))
        fib = (chi == 1 and clo == 1)
        rank = hi - lo if fib else None
        print(f'psi=(1,{k:2d}) word={w} max={hi}x{chi} min={lo}x{clo} '
              f'fibred={fib} rank={rank} alexander n={width(1, k) + 1}')
    w, hi, chi, lo, clo = summary(rewrite_t_direction())
    print('psi_0=(0,1) word in b_i =', w, f'max={hi}x{chi} min={lo}x{clo}')
