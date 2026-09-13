#!/usr/bin/env python3
"""The length-15 residue of the unpeelable census, generated from its normal form.

Magnus sequence (scripts' convention a_h = t^h a t^-h): a_1^e a_0^x1 a_2^x2 a_0^x3 a_2^x4,
{|x1|,|x3|} = {|x2|,|x4|} = {1,2}, exponents not all of one sign.  Classes are taken
up to census.canon.  For each class print the relator, whether a partially positive
Whitehead image of length <= 19 exists (census2.pp_search, extra 4, cap 20000), the
Alexander polynomial Delta(t) = sum_h delta_h t^h of chi, and H_1 torsion |Delta(1)|.
Usage: residue.py
"""
import census as C
import census2 as C2

def family():
    S = (1, -1, 2, -2)
    for e in (1, -1):
        for x1 in S:
            for x3 in S:
                if {abs(x1), abs(x3)} != {1, 2}:
                    continue
                for x2 in S:
                    for x4 in S:
                        if {abs(x2), abs(x4)} != {1, 2}:
                            continue
                        yield (e, x1, x2, x3, x4)

def main():
    classes = {}
    for ex in family():
        e, x1, x2, x3, x4 = ex
        seq = [(1, e), (0, x1), (2, x2), (0, x3), (2, x4)]
        classes.setdefault(C.canon(seq), ex)
    print('classes=%d' % len(classes))
    rest = 0
    for c in sorted(classes):
        ex = classes[c]
        cs = list(c)
        w = C.seq_to_word(cs)
        allsign = all(x > 0 for x in ex) or all(x < 0 for x in ex)
        C.BUDGET[0] = 3000
        ok, why = C.cert_word(w, 0)
        v = None if allsign else C2.pp_search(w, 4, 20000)
        delta = [0, 0, 0]
        for h, k in cs:
            delta[h] += k
        tors = abs(sum(delta))
        cyc = ''
        if abs(delta[0]) == 1 and delta[0] == delta[2]:
            cyc = 'Phi3' if delta[1] == delta[0] else 'Phi6'
        tag = 'PP' if allsign else ('PPIMG ' + C.word_str(v) if v is not None else 'REST')
        if tag == 'REST':
            rest += 1
        print('CLASS %s len=%d ex=%s seq=%s cert=%s delta=%s tors=%d cyc=%s %s'
              % (C.word_str(w), len(w), ex, cs, ok, delta, tors, cyc or '-', tag), flush=True)
    print('rest=%d' % rest)
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
