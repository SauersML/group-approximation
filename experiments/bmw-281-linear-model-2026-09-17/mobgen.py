# semilinear Iwahori-type Moebius group on O/s^m, O=F3[[s]]; point index = sum x_i 3^(m-1-i) + 1
import sys, itertools
m = int(sys.argv[1]); var = sys.argv[2] if len(sys.argv)>2 else 'aff'
pts = list(itertools.product(range(3), repeat=m))
def idx(c): return sum(c[i]*3**(m-1-i) for i in range(m))
def mul(a,b):
    r=[0]*m
    for i in range(m):
        if a[i]:
            for j in range(m-i): r[i+j]=(r[i+j]+a[i]*b[j])%3
    return r
def inv(a):
    r=[0]*m; r[0]=a[0]
    for k in range(1,m):
        s=sum(a[i]*r[k-i] for i in range(1,k+1))%3
        r[k]=(-s*r[0])%3
    return r
def add(a,b): return [(x+y)%3 for x,y in zip(a,b)]
def mono(i,c=1): return [c if j==i else 0 for j in range(m)]
def mob(al,be,ga,de):
    return [idx(mul(add(mul(al,list(x)),be), inv(add(mul(ga,list(x)),de)))) for x in pts]
one=mono(0); zero=[0]*m
gens=[]
for i in range(m):
    gens.append(mob(one,mono(i),zero,one))          # x + s^i
    if i>=1:
        gens.append(mob(add(one,mono(i)),zero,zero,one))  # (1+s^i) x
        gens.append(mob(one,zero,mono(i),one))           # x/(s^i x + 1)
gens.append(mob(mono(0,2),zero,zero,one))  # -x
gens.append([idx(tuple((c[j]*(-1)**j)%3 for j in range(m))) for c in pts])  # sigma
print('mob:=[' + ','.join('PermList([' + ','.join(str(i+1) for i in g) + '])' for g in gens) + '];')
