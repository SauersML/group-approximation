#!/usr/bin/env python3
"""Per-relator verdict for the 96 length-23 three-level (n = 3) relators.

For each relator w of w23n3.cert (all OPEN: census.cert_word, budget 4000, finds nothing) it
picks a presentation P of G = <a,t | w>:
  * P = w itself, if topsz.py (top96.out) gives finite sZ(psi) and sZ(psi^-1);
  * otherwise P = w' from rebased80.txt, the image of w under the automorphism a -> a,
    t -> t a^-1 of F(a,t) (so y = t a is the new stable letter; <a,t|w> = <a,y|w'>), with
    its top sZ read from top_rebased80.out.
It then requires, in the SAME presentation P:
  * TOP: both sZ values finite (two 'PASS sZ=' fields; the tuple is
         (sZ(psi), sZ(psi^-1), rank(A cap B), certify verdicts with the inner depths f', f''));
  * L1:  level1.py reports ZSTABLE (a zero-exponent letter s of W_0 along which the rewritten
         relator is primitive, with finite sZ both ways);
and, for G itself (an isomorphism invariant, keyed by the original w):
  * KB:  kbmag AUTOMATIC HYPERBOLIC (kb96.out, default; kb29large.out, autgroup -large).
Prints one line per relator and a summary; exits 1 unless all 96 pass."""
import sys, os
D = os.path.dirname(os.path.abspath(__file__))


def rd(name):
    return [l.rstrip('\n') for l in open(os.path.join(D, name)) if l.strip()]


def tops(name):
    r = {}
    for l in rd(name):
        if l.startswith('TOP '):
            w = l.split()[1]; tail = l.rsplit('->', 1)[1].strip()
            r[w] = tail if tail.count("'PASS sZ=") == 2 else None
    return r


def l1s(name):
    r = {}
    for l in rd(name):
        if l.startswith('L1 '):
            w = l.split()[1]; tail = l.rsplit('->', 1)[1].strip()
            r[w] = tail if tail.startswith('ZSTABLE') else None
    return r


def kbs(*names):
    r = {}
    for n in names:
        for l in rd(n):
            if l.startswith('KB ') and 'AUTOMATIC HYPERBOLIC' in l:
                orig = [f for f in l.split() if f.startswith('orig=')][0][5:]
                opt = l.split('opt=')[1].split(' ', 1)[0]
                r[orig] = n + ':' + (opt or 'default')
    return r


words = [l.split()[1] for l in rd('w23n3.cert') if l.startswith('OPEN')]
nopen = len(words)
reb = {}
for l in rd('rebased80.txt'):
    new, old = l.split(); reb[old] = new
T0, T1 = tops('top96.out'), tops('top_rebased80.out')
L0, L1 = l1s('l1_96.out'), l1s('l1_rebased80.out')
KB = kbs('kb96.out', 'kb29large.out')
ok = 0; cnt = {}
for w in words:
    if T0.get(w):
        P, pres, top, l1 = w, 'orig', T0[w], L0.get(w)
    elif w in reb:
        P = reb[w]; pres, top, l1 = 'y=ta', T1.get(P), L1.get(P)
    else:
        P, pres, top, l1 = w, 'none', None, None
    kb = KB.get(w)
    good = bool(top and l1 and kb)
    ok += good
    from ast import literal_eval
    tt = literal_eval(top) if top else None
    key = (pres, 'sZ=(%d,%d) rkD=%d' % tt[:3] if tt else None, l1)
    cnt[key] = cnt.get(key, 0) + 1
    print('%s %s pres=%s P=%s top=%s l1=%s kb=%s' % ('PASS' if good else 'FAIL', w, pres, P, top, l1, kb))
print('census OPEN %d; certified %d of %d' % (nopen, ok, len(words)))
for k in sorted(cnt, key=str):
    print('  %-5s top %-16s l1 %-18s : %d' % (k[0], k[1], k[2], cnt[k]))
sys.exit(0 if ok == len(words) == 96 else 1)
