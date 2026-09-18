"""Post-process brratio output: TJT, Br/TJT, jackknife errors.
usage: python3 ana.py file [file ...]   (files from the same parameters are pooled)"""
import sys, math
def load(fn):
    hdr=None; rows=[]
    for l in open(fn):
        if l.startswith('#'): hdr=dict(kv.split('=') for kv in l[1:].split())
        elif l.startswith('B'):
            p=l.split(); rows.append((int(p[1]),list(map(float,p[2:]))))
    return hdr,rows
def stats(hdr,x):
    typ=int(hdr['type']); n=int(hdr['n']); NV=int(hdr['NV']); P=int(hdr['P'])
    tu=x[:NV]; tv=x[NV:2*NV]; Tuv=x[2*NV]; Br=x[2*NV+1]; q=x[2*NV+2]; th=x[2*NV+3]; brk=x[2*NV+4:]
    if typ==0: edges=[(k-1,k) for k in range(1,n+1)]
    else: edges=[(k-1,k%P) for k in range(1,P+1)]
    tjt=0; endp=0
    for (a,b) in edges:
        for (x_,y_) in ((a,b),(b,a)):
            val=tu[x_]*tv[y_]; tjt+=val
            if x_==0 or y_==n: endp+=val
    return dict(Tuv=Tuv,Br=Br,TJT=tjt,endfrac=endp/tjt,ratio=Br/tjt,BrT=Br/Tuv,TJTT=tjt/Tuv,q=q,theta=th,
                K2=(Tuv/(tu[n//2]*tv[n//2]) if typ==0 else float('nan')),
                lam=(tu[n]/tu[n-1] if typ==0 else float('nan')))
def main(fns):
    hdr=None; rows=[]
    for fn in fns:
        h,r=load(fn); hdr=hdr or h; rows+=r
    W=sum(w for w,_ in rows); L=len(rows[0][1])
    mean=[sum(w*v[i] for w,v in rows)/W for i in range(L)]
    full=stats(hdr,mean)
    # jackknife over batches
    jk={k:[] for k in full}
    for j,(wj,vj) in enumerate(rows):
        m=[(mean[i]*W-wj*vj[i])/(W-wj) for i in range(L)]
        s=stats(hdr,m)
        for k in s: jk[k].append(s[k])
    B=len(rows); err={}
    for k in full:
        mu=sum(jk[k])/B; err[k]=math.sqrt((B-1)/B*sum((z-mu)**2 for z in jk[k])) if B>1 else float('nan')
    return hdr,full,err,W
if __name__=='__main__':
    hdr,full,err,W=main(sys.argv[1:])
    print('type=%s n=%s h=%s pp=%s r=%s M=%s envs=%d'%(hdr['type'],hdr['n'],hdr['h'],hdr['pp'],hdr['r'],hdr['M'],W))
    for k in ['ratio','BrT','TJTT','endfrac','Tuv','q','theta','K2']:
        print('  %-8s %.5g +- %.2g'%(k,full[k],err[k]))
