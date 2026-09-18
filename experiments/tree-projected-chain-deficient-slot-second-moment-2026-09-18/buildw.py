import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'tree-projected-pollard-slot-second-moment-2026-09-18'))
import sys, pickle, time
import engine_w as E
E.NZREF = E.RIGID = E.POL = E.NONAP = True
E.PW = True; E.WAUG = True; E.WPW = True
m = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 1
t0 = time.time()
E.M_REF = m
E._cb_memo.clear(); E.W_AGG.clear()
TE, ncl = E.pair_terms(1, K, (-1, 0, 1))
pickle.dump((TE, ncl, dict(E.W_AGG)), open('termsWPW_K%d_m%d.pkl' % (K, m), 'wb'))
print('built in', round(time.time() - t0), 's; terms', len(TE), 'W terms', len(E.W_AGG), flush=True)
