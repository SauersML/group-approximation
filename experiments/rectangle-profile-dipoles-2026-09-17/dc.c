/* Double covers of square-tiled tori branched at two vertices 0,g.
   G = Z^2/Lambda, Lambda=<(N1,0),(c,N2)>.  Rectangle word [b^s,c^t] has
   rank = |R_{s,t} xor (g+R_{s,t})|, R_{s,t} = sum_{i<s,j<t} X^i Y^j mod 2.
   Prints per (lattice,g): N1 N2 c g |g|_1 maxrank_over(s+t) argmax s t   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int N,N1,N2,C,*Xs,*Ys,*add;
int main(int argc,char**argv){
  int Nmin=atoi(argv[1]),Nmax=atoi(argv[2]);
  for(N=Nmin;N<=Nmax;N++) for(N1=1;N1<=N;N1++){ if(N%N1)continue; N2=N/N1;
   for(C=0;C<N1;C++){
    Xs=malloc(N*sizeof(int));Ys=malloc(N*sizeof(int));add=malloc(N*N*sizeof(int));
    for(int y=0;y<N2;y++)for(int x=0;x<N1;x++){int h=y*N1+x;Xs[h]=y*N1+(x+1)%N1;
      Ys[h]= (y+1<N2)? (y+1)*N1+x : ((x-C)%N1+N1)%N1; }
    /* coordinates -> addition table: element h = x + y*(1,0).. build by BFS words */
    int *px=malloc(N*sizeof(int)),*py=malloc(N*sizeof(int));
    for(int y=0;y<N2;y++)for(int x=0;x<N1;x++){px[y*N1+x]=x;py[y*N1+x]=y;}
    for(int a=0;a<N;a++)for(int b=0;b<N;b++){int h=a;for(int i=0;i<px[b];i++)h=Xs[h];for(int j=0;j<py[b];j++)h=Ys[h];add[a*N+b]=h;}
    int oX=N1,oY=0,h=0;do{h=Ys[h];oY++;}while(h!=0);
    /* L1 norm BFS with X^-1,Y^-1 */
    int *Xi=malloc(N*sizeof(int)),*Yi=malloc(N*sizeof(int)),*dist=malloc(N*sizeof(int)),*q=malloc(N*sizeof(int));
    for(int k=0;k<N;k++){Xi[Xs[k]]=k;Yi[Ys[k]]=k;dist[k]=-1;}
    int qh=0,qt=0;q[qt++]=0;dist[0]=0;while(qh<qt){int u=q[qh++];int nb[4]={Xs[u],Ys[u],Xi[u],Yi[u]};for(int k=0;k<4;k++)if(dist[nb[k]]<0){dist[nb[k]]=dist[u]+1;q[qt++]=nb[k];}}
    double *best=calloc(N,sizeof(double));int *bs=calloc(N,sizeof(int)),*bt=calloc(N,sizeof(int));
    char *Rs=calloc(N,1),*R=malloc(N);int *lst=malloc(N*sizeof(int));
    int xp=0; /* X^{s-1} applied to 0 */
    for(int s=1;s<=2*oX;s++){ Rs[xp]^=1; xp=Xs[xp];
      memset(R,0,N); char *Tt=malloc(N); memcpy(Tt,Rs,N);
      for(int t=1;t<=2*oY;t++){
        for(int k=0;k<N;k++)R[k]^=Tt[k];
        {char*nt=calloc(N,1);for(int k=0;k<N;k++)if(Tt[k])nt[Ys[k]]=1;free(Tt);Tt=nt;}
        int m=0;for(int k=0;k<N;k++)if(R[k])lst[m++]=k;
        for(int g=1;g<N;g++){int A=0;for(int i=0;i<m;i++)A+=R[add[lst[i]*N+g]];
          double r=2.0*(m-A)/(s+t); if(r>best[g]){best[g]=r;bs[g]=s;bt[g]=t;}}
      }
      free(Tt);
    }
    for(int g=1;g<N;g++) printf("%d %d %d %d %d %d %.4f %d %d\n",N,N1,C,g,px[g]*0+g,dist[g],best[g],bs[g],bt[g]);
    free(Xs);free(Ys);free(add);free(px);free(py);free(Xi);free(Yi);free(dist);free(q);free(best);free(bs);free(bt);free(Rs);free(R);free(lst);
   }}
  return 0;}
