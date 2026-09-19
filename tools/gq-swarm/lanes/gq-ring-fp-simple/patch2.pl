s/WIDE = len\(sys\.argv\) > 5 and sys\.argv\[5\] == 'wide'\n/WIDE = len(sys.argv) > 5 and sys.argv[5] == 'wide'\nCALIB = len(sys.argv) > 5 and sys.argv[5] == 'calib'  # adds e = diag(2,1): hits MUST appear\n/;
s/for M in \(Wm, Dm\):\n    GENS\.append\(\(0, M\)\)\n/for M in (Wm, Dm):\n    GENS.append((0, M))\nEm = ((2, 0), (0, 1))\nif CALIB:\n    GENS.append((0, Em))\n/;
s/    if M in \(Wm, Dm\):\n        INV\.append\(GENS\.index\(g\)\)/    if M in (Wm, Dm, Em):\n        INV.append(-1 if M == Em else GENS.index(g))/;
s/Y2i: 'q', Wm: 'W', Dm: 'D'\}/Y2i: 'q', Wm: 'W', Dm: 'D', Em: 'E'}/;
