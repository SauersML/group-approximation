import sys, itertools
k,r=int(sys.argv[1]),int(sys.argv[2])
out=open(sys.argv[3],'w')
def gen(i,rem,z):
    if i<0:
        for t in range(k-1,-1,-1):
            if z[t]!=0:
                if z[t]>0: out.write(' '.join(map(str,z))+'\n')
                return
        return
    for v in range(-rem,rem+1):
        z[i]=v; gen(i-1,rem-abs(v),z)
    z[i]=0
gen(k-1,r,[0]*k)
