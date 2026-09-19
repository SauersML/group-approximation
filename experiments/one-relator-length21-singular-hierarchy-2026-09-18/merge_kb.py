#!/usr/bin/env python3
"""Merge the hyperbolicity evidence for the relators of rel821.txt into one verdict per relator.
Sources, in order of preference:
  kbmag   : kbhyp.sh on w itself (files kb_*.out, lines "KB w AUTOMATIC HYPERBOLIC ...")
  kbswap  : kbretry.sh on w with a<->t renamed (kbretry_r1.out, kbr_*.out, "... ORIG w")
  kblarge : kbhyp2.sh with AUTOPT=-large, SWAP=0/1, and for the last 14 the word-difference cap
            raised to MWD=8192 via autgroup_mwd.sh (kb2_*.out, "... orig=w")
  C'(1/6) : smallcanc.py (sc821.out, "C6=True")
Output (stdout): "w HYPERBOLIC <source> <detail>" or "w UNRESOLVED"; summary on stderr.
The per-run files are reproduced section by section ("== <file>") in kbraw.out.
Usage: merge_kb.py  (run in the directory holding the per-run files)"""
import glob, re, sys
rels = [l.split()[0] for l in open('rel821.txt') if l.strip()]
got = {}


def note(w, src, det):
    if w in rels and w not in got:
        got[w] = (src, det)


def hyp_lines(files):
    for f in sorted(files):
        for l in open(f):
            if l.startswith('KB ') and 'AUTOMATIC HYPERBOLIC' in l:
                yield l.rstrip('\n')


for l in hyp_lines(glob.glob('kb_kb*.out')):
    note(l.split()[1], 'kbmag', re.search(r'\((.*?)\)', l).group(1))
for l in hyp_lines(['kbretry_r1.out'] + glob.glob('kbr_*.out')):
    note(l.split()[-1], 'kbswap', 'renamed ' + l.split()[1] + ' ' + re.search(r'\((.*?)\)', l).group(1))
for l in hyp_lines(glob.glob('kb2_*.out')):
    m = re.search(r'opt=(\S*) swap=(\S*) (?:mwd=(\S+) )?orig=(\S+)', l)
    note(m.group(4), 'kblarge', 'autgroup ' + m.group(1) + ' swap=' + m.group(2) +
         ' mwd=' + (m.group(3) or '512') + ' ' +
         re.search(r'\((.*?)\)', l).group(1))
for l in open('sc821.out'):
    if l.startswith('SC ') and 'C6=True' in l:
        note(l.split()[1], "C'(1/6)", re.search(r'maxpiece=\d+', l).group(0))
cnt = {}
for w in rels:
    if w in got:
        s, d = got[w]
        print(w, 'HYPERBOLIC', s, d)
        cnt[s] = cnt.get(s, 0) + 1
    else:
        print(w, 'UNRESOLVED')
        cnt['UNRESOLVED'] = cnt.get('UNRESOLVED', 0) + 1
print('total', len(rels), cnt, file=sys.stderr)
