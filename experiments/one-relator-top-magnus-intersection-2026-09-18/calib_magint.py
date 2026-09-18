"""Calibration of magint.decide on hand-checkable pieces with n = 2 (letters 1,2,3 = a0,a1,a2).
  comm: W0 = [a0,a1][a2,a1]: [a0,a1] = [a1,a2] lies in A cap B but not in <a1>, so the
        intersection is exceptional; decide must NOT return NONEXC.
  free: W0 = a0 a2 A0 A2 a1: B0 = F(a0,a2), a1 = [a2,a0]; A cap B = <a1> (non-exceptional)."""
import magint as M
T = {'comm': [1, 2, -1, -2, 3, 2, -3, -2], 'free': [1, 3, -1, -3, 2]}
for k, W in T.items():
    for s, Ml, Nl in ((1, {1, 2}, {2, 3}), (3, {2, 3}, {1, 2})):
        print('CALIB', k, 's=a%d' % (s - 1), *M.decide(2, W, s, Ml, Nl))
print('SENTINEL_DONE')
