"""Probe specific words: contact ranks and malnormality of H_s = <s, v>."""
import sys
from census import analyse
from stallings import malnormal, fold, core

words = sys.argv[1:] or ['cdcDcd', 'cdcDD', 'cdcDDd', 'ccdcd', 'cdcdd']
for w in words:
    ff, hits = analyse(w)
    out = [w, 'freefactor' if ff else '']
    for s in 'cd':
        H = [s, w]
        G, b = fold(H)
        out.append('H_%s: size %d malnormal %s' % (s, len(core(G, b)), malnormal(H)[0]))
    out.append('contacts ' + str(hits))
    print(' | '.join(out))
