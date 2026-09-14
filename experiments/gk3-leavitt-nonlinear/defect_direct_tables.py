import os, sys
R = '/Users/user/nonsofic_existence/experiments'
os.environ['LEAVITT_LIB'] = R + '/nonsofic-certificates'
for p in ('/nonsofic-certificates', '/gottschalk-small-presentations', '/gk3-leavitt-nonlinear'):
    sys.path.insert(0, R + p)
import general_window_screen as GW
L = GW.L
L.set_dual(True)
U = GW.extra_units(GW.W.named_units())
I, a, l = L.IDENTITY, U['ca'], U['E01_1']
print('l^2 == 1:', (l * l).is_identity(), '  l == 1:', l.is_identity())
print('a^k == 1 for k=1..8:', [(a ** k).is_identity() for k in range(1, 9)])
d = GW.defect_element(U, 'E01_1')
print('defect d01 == 1:', d.is_identity())
S = [('1', I), ('a', a), ('A', a.inverse()), ('al', a * l.inverse())]
M = [('1', I), ('l', l), ('a', a)]
for tag, left, right in (('forward S x M', S, M), ('reverse M x S', M, S)):
    classes = {}
    for na, xa in left:
        for nb, xb in right:
            classes.setdefault((xa * xb).key, []).append('(%s,%s)' % (na, nb))
    print(tag, 'classes:', len(classes), 'of', len(left) * len(right))
    for k, v in classes.items():
        if len(v) > 1:
            print('   coincide:', ' = '.join(v), '  (= 1)' if k == I.key else '')
print('dual stats:', L.dual_stats())
