"""Malnormality of the letter subgroups H_s = <s, v> for the sharp-test word
v = cdcDcd, with the known malnormal control K = <c, dcDD> (= <a, bab^-2>)
and the non-malnormal control <c, dd>."""
from stallings import fold, malnormal, core

tests = {
    'H_c = <c, cdcDcd>': ['c', 'cdcDcd'],
    'H_d = <d, cdcDcd>': ['d', 'cdcDcd'],
    'control K = <c, dcDD>': ['c', 'dcDD'],
    'control <c, dd> (not malnormal)': ['c', 'dd'],
    '<v> = <cdcDcd>': ['cdcDcd'],
}
for name, ws in tests.items():
    G, b = fold(ws)
    print(name, 'stallings vertices', G.n, 'core', len(core(G, b)),
          'malnormal', malnormal(ws))
