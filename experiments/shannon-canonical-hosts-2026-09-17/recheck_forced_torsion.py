#!/usr/bin/env python3
"""Re-derive the canonical host of every fake listed in scan_*.txt and check that its torsion certificate
is realization independent.

A certificate (u, k) says u^k = 1 in the canonical host H_P, hence in every group realizing the pattern P
(every realization receives a homomorphism from H_P that is the identity on letters). It forces torsion in
every realization when u, up to cyclic rotation and inversion, is one of
  f e      with f e != 1 in the pattern   (a window point other than 1; realizations keep which products are 1)
  f f'^-1  or f^-1 f'  with f != f'       (readers are distinct in every realization)
  e e'^-1  or e^-1 e'  with e != e'       (offsets are distinct in every realization)
Then u is nontrivial with u^k = 1 in every realization, so P occurs in no torsion-free group.

usage: recheck_forced_torsion.py scan_*.txt
"""
import sys, os, re, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from random_scan import Cyc, Perm
from torsion2_scan import Z2k, Dinf
from host_tietze import classify, word_str, power_root
from fake_hosts_scan import Prod


def group_and_parser(name):
    if re.fullmatch(r'z\d+', name):
        return Cyc(int(name[1:])), int
    if name == 'z7fake':
        return Cyc(7), int
    if name == 'k2':
        return Z2k(2), lambda s: tuple(int(c) for c in s)
    if name == 's3':
        return Perm(3, None), lambda s: tuple(int(c) for c in s)
    if name == 'z2z4':
        return Prod(Cyc(2), Cyc(4)), lambda s: tuple(int(c) for c in s.strip('()').split(','))
    if name == 'z3z3':
        return Prod(Cyc(3), Cyc(3)), lambda s: tuple(int(c) for c in s.strip('()').split(','))
    if name == 's4':
        return Perm(4, None), lambda s: tuple(int(c) for c in s)
    if name == 'heis3':
        from random_fake_hosts import Heis3
        return Heis3(), lambda s: tuple(int(c) for c in s)
    if name == 'dinf7':
        def p(s):
            return (-1, int(s[1:])) if s.startswith('r') else (1, int(s))
        return Dinf(), p
    raise ValueError(name)


def split_set(s):
    s = s[1:-1]
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur); cur = ''
        else:
            cur += ch
    out.append(cur)
    return out


def forced(G, E, F, names, u):
    nE = len(dict.fromkeys(E))
    if len(u) != 2:
        return False
    (a, sa), (b, sb) = u
    kinds = {a: 'e' if a < nE else 'f', b: 'e' if b < nE else 'f'}
    image = list(dict.fromkeys(E)) + list(dict.fromkeys(F))
    if a == b:
        return False
    ka, kb = kinds[a], kinds[b]
    if ka != kb:
        if sa != sb:
            return False
        f = a if ka == 'f' else b
        e = b if ka == 'f' else a
        return G.mul(image[f], image[e]) != G.one
    return sa == -sb  # two distinct letters of the same kind, opposite signs


def cert_kind(E, u):
    nE = len(dict.fromkeys(E))
    (a, _), (b, _) = u
    ka, kb = ('e' if a < nE else 'f'), ('e' if b < nE else 'f')
    if ka != kb:
        return 'point'
    return 'offset-ratio' if ka == 'e' else 'reader-ratio'


def main():
    total, ok = 0, 0
    bad = []
    table = {}
    for path in sys.argv[1:]:
        for line in open(path):
            m = re.match(r'^(\S+) E=(\{.*?\}) F=(\{.*?\}) n=(\d+) LP=([\d.]+)', line)
            if not m:
                continue
            name = m.group(1)
            G, parse = group_and_parser(name)
            E = [parse(s) for s in split_set(m.group(2))]
            F = [parse(s) for s in split_set(m.group(3))]
            kind, names, alive, red, cert = classify(G, E, F)
            total += 1
            good = bool(cert) and forced(G, E, F, names, cert[0])
            rng = random.Random(0)
            for _ in range(300):
                if good:
                    break
                # retry with a shuffled elimination order; every run is a sequence of Tietze moves on H_P
                kind2, names2, alive2, red2, _ = classify(G, E, F, rng)
                for rel in red2:
                    u, k = power_root(rel)
                    if k >= 2 and forced(G, E, F, names2, u):
                        good, cert, names = True, (u, k), names2
                        print('retry certificate: %s  (%s)^%d' % (line.strip(), word_str(names2, u), k))
                        break
            if good:
                ok += 1
                ck = cert_kind(E, cert[0])
                print('CERT %s %s LP=%s host=%s  (%s)^%d  [%s]' % (name, m.group(2) + ' ' + m.group(3), m.group(5),
                      kind, word_str(names, cert[0]), cert[1], ck))
                row = table.setdefault(name, {})
                row[(ck, cert[1])] = row.get((ck, cert[1]), 0) + 1
            else:
                bad.append((line.strip(), kind, [word_str(names, r) for r in red]))
    for name, row in table.items():
        print('TABLE %s: %s' % (name, ', '.join('%s order %d: %d' % (ck, k, c) for (ck, k), c in sorted(row.items()))))
    print('fakes rechecked: %d; torsion forced in every realization by a two-letter certificate: %d' % (total, ok))
    for b in bad:
        print('NOT CERTIFIED:', b)


if __name__ == '__main__':
    main()
