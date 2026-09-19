# Train-track coordinates.  theta = (Nielsen move s -> q s) o (s -> s r), found by tt_search.py (depth 2);
# psi = theta phi theta^-1 is a train-track map of the rose.
import sys
sys.path.insert(0, '.')
from fbc import tofib, apply, PHI, PHII, red, inv
L = 'pqrs'
def comp(m1, m2): return {c: apply(m1, m2[c]) for c in L}
TH = {'p': 'p', 'q': 'q', 'r': 'r', 's': 'qsr'}
THI = {'p': 'p', 'q': 'q', 'r': 'r', 's': 'QsR'}
assert all(apply(TH, apply(THI, c)) == c and apply(THI, apply(TH, c)) == c for c in L)
PSI = comp(TH, comp(PHI, THI))
assert PSI == {'p': 'q', 'q': 'r', 'r': 'qsr', 's': 'SPR'}
A, B, Cc, E = tofib('XyxYx'), tofib('XyyyxYYY'), tofib('XYxyx'), tofib('xyXY')
def pw(u, j):
    for _ in range(abs(j)): u = apply(PHI if j > 0 else PHII, u)
    return u
