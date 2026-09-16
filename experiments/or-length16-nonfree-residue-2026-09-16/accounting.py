#!/usr/bin/env python3
"""Bookkeeping for the 211 length-16 residue classes.

Reads
  census3_16.out  (landed: the 211 REST words of the length-16 unpeelable residue),
  lg_words16.out  (landed: 70 '-> PASS', 141 NONFREE),
  primcert.out    (this lane: transported Linton certificate on the 141),
  VF_OUTS         (comma-separated vfib.py outputs of this lane, CERT lines),
  VERIFY_OUTS     (comma-separated verify.py outputs on those files),
  RECHECK_OUT     (recheck.py, the independently written checker, on the same files),
and checks:
  * the 70 + 141 words of lg_words16.out are exactly the 211 REST words of census3_16.out;
  * the 141 NONFREE words of lg_words16.out are exactly the words of primcert.out, and the 70 PASS
    words are disjoint from them;
  * primcert.out has 34 PASS words; the other 107 ('open') are FAIL/PASS_HLOOP or NONPRIM;
  * every VERIFIED word has exactly one CERT line over all VF_OUTS, on the word itself (no
    automorphic image), and is one of the 211 words;
  * every VERIFIED word is cyclically reduced, uses both letters, and is not a proper power (for a
    cyclically reduced word: not a repetition u^m, m >= 2, of a string u);
  * every VERIFIED word is RECHECKED by recheck.py with the same index k, the same span S and
    fibre rank n = 1 - chi(X[0,S]), and recheck.py accepts nothing else;
  * every open word is VERIFIED.
Prints the per-class lists used by research/artifacts/or-length16-nonfree-residue-2026-09-16.md.
Usage: accounting.py CENSUS3_16_OUT LG_WORDS16_OUT PRIMCERT_OUT VF_OUTS VERIFY_OUTS RECHECK_OUT
"""
import sys


def cyc_reduced(w):
    inv = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}
    return all(w[i] != inv[w[(i + 1) % len(w)]] for i in range(len(w)))


def proper_power(w):
    n = len(w)
    return any(n % d == 0 and w == w[:d] * (n // d) for d in range(1, n))


def main():
    cen, lg, pc, vfs, vers, rec = sys.argv[1:7]
    rest = []
    for line in open(cen):
        f = line.split()
        if f and f[0] == 'REST':
            rest.append(f[1])
    landed_pass, nonfree = [], []
    for line in open(lg):
        f = line.split()
        if f and f[0] == 'VERDICT':
            if f[-1] == 'NONFREE':
                nonfree.append(f[2])
            elif line.rstrip().endswith('-> PASS'):
                landed_pass.append(f[3])
    prim_pass, prim_other, nonprim = [], [], []
    for line in open(pc):
        f = line.split()
        if f and f[0] == 'VERDICT':
            verdict = line.rstrip().split('-> ')[-1].replace(' ', '_')
            (prim_pass if verdict == 'PASS' else prim_other).append((f[2], verdict))
        elif f and f[0] == 'NONPRIM':
            nonprim.append(f[1])
    certs = {}
    for fn in vfs.split(','):
        for line in open(fn):
            f = line.split()
            if f and f[0] == 'CERT':
                certs.setdefault(f[1], []).append(line.rstrip())
    verified = {}
    for fn in vers.split(','):
        for line in open(fn):
            f = line.split()
            if len(f) >= 2 and f[1] == 'VERIFIED':
                assert f[0] not in verified, f[0]
                verified[f[0]] = ' '.join(f[2:])
    rechecked = {}
    for line in open(rec):
        f = line.split()
        if len(f) >= 2 and f[1] == 'RECHECKED':
            assert f[0] not in rechecked, f[0]
            rechecked[f[0]] = (f[2], f[3], 1 - int(f[4].split('=')[1]))
    assert set(rechecked) == set(verified), sorted(set(rechecked) ^ set(verified))
    for w, txt in verified.items():
        k, S, fib = txt.split()
        assert (k, S, int(fib.split('_')[1])) == rechecked[w], (w, txt, rechecked[w])
    allprim = [w for w, _ in prim_pass] + [w for w, _ in prim_other] + nonprim
    assert len(landed_pass) == 70 and len(nonfree) == 141, (len(landed_pass), len(nonfree))
    assert sorted(allprim) == sorted(nonfree)
    assert not set(landed_pass) & set(nonfree)
    allw = set(landed_pass) | set(nonfree)
    assert len(allw) == 211
    assert len(rest) == 211 and set(rest) == allw
    passw = set(w for w, _ in prim_pass)
    openw = set(w for w, _ in prim_other) | set(nonprim)
    assert len(passw) == 34 and len(openw) == 107
    assert set(verified) <= allw
    for w in verified:
        assert len(certs[w]) == 1, w
        assert certs[w][0].split()[1] == w
        assert cyc_reduced(w) and set(w.lower()) == {'a', 't'} and not proper_power(w), w
    for w in passw:
        assert cyc_reduced(w) and not proper_power(w), w
    assert openw <= set(verified)
    print('CENSUS_REST %d = LANDED_PASS %d + NONFREE %d' % (len(rest), len(landed_pass), len(nonfree)))
    for w, v in prim_pass:
        print('PRIMPASS %s vfib=%s' % (w, verified.get(w, 'NONE_AT_SEARCHED_INDEX').replace(' ', ',')))
    for w, v in prim_other:
        print('PRIMOTHER %s %s VERIFIED %s' % (w, v, verified[w]))
    for w in sorted(nonprim):
        print('NONPRIM %s VERIFIED %s' % (w, verified[w]))
    for w in landed_pass:
        print('LANDEDPASS %s vfib=%s' % (w, verified.get(w, 'NONE_AT_SEARCHED_INDEX').replace(' ', ',')))

    def ks(ws):
        out = {}
        for w in ws:
            if w in verified:
                k = verified[w].split()[0]
                out[k] = out.get(k, 0) + 1
        return sorted(out.items(), key=lambda kv: int(kv[0][2:]))

    vl = [w for w in landed_pass if w in verified]
    vp = [w for w in passw if w in verified]
    print('COUNTS open=%d open_verified=%d index=%s' % (len(openw), len(openw & set(verified)), ks(openw)))
    print('COUNTS primpass=%d primpass_verified=%d index=%s' % (len(passw), len(vp), ks(passw)))
    print('COUNTS landedpass=%d landedpass_verified=%d index=%s' % (len(landed_pass), len(vl), ks(landed_pass)))
    nov = sorted(allw - set(verified))
    print('NO_VFIB_CERT %d (all Linton-certified): %s' % (len(nov), ' '.join(nov)))
    print('RECHECKED %d (same k, S, fibre rank as verify.py)' % len(rechecked))
    print('TOTAL virtually free-by-cyclic by verified certificate: %d of 211' % len(verified))
    print('TOTAL Linton-certified (landed 70 + transported 34): %d of 211' % (70 + len(passw)))
    print('TOTAL covered by at least one certificate: %d of 211' % len(set(verified) | passw | set(landed_pass)))
    print('SENTINEL_DONE')


if __name__ == '__main__':
    main()
