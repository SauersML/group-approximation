"""Probe: is the lp5 certificate LP ever feasible for a positive *automorphism* (any, even
reducible/geometric)?  Endomorphism controls are included for comparison.
usage: python3 probe_auts.py maxlen maxdarts tl"""
import sys, json
from ffold import *
from lp_census import scan
AUT = [{"a":"ab","b":"a","c":"c"}, {"a":"ab","b":"b","c":"c"}, {"a":"abc","b":"b","c":"c"},
       {"a":"ab","b":"bc","c":"c"}, {"a":"b","b":"c","c":"ab"}, {"a":"ab","b":"ac","c":"a"},
       {"a":"bbc","b":"bbcb","c":"cbba"}, {"a":"abb","b":"ab","c":"c"}]
END = [{"a":"ab","b":"ba","c":"c"}, {"a":"abb","b":"ba","c":"c"}, {"a":"aab","b":"bab","c":"c"}]
maxlen, maxdarts, tl = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
for tag, L in (("aut", AUT), ("end", END)):
    for phi in L:
        aut = stallings_is_whole_group([phi[x] for x in "abc"])
        for m in (1, 2, 3):
            print(tag, phi, "is_aut", aut, "m", m, *scan(phi, m, maxlen, maxdarts, tl), flush=True)
