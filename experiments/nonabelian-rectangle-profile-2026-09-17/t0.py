from perm import *
for g in ['S3','Q8','A4','Z2']:
    els,mul=named_group(g); print(g,len(els))
# slit origami Z2 on 12x12 torus with slit length L
els,mul=named_group('Z2')
for L in [2,4,6]:
    T=Torus(12,12,0); beta=[0]*T.N; gamma=[0]*T.N
    for i in range(L): gamma[T.idx(i+1,0)]=1
    b,c=cover(T,mul,beta,gamma)
    print(L, profile(b,c), best_rounding(b,c,1))
