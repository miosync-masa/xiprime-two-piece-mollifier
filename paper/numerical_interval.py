"""Independent Taylor/interval enclosure of the equal-length leading pole.

No quadrature: integrate polynomials by beta integrals. Intervals use mpmath.iv
outward-rounded arithmetic; analytic Taylor tails are added explicitly.
This certifies the displayed main-term functional, not its analytic transfer.
"""
import math
from mpmath import iv


def enclosure(dps=55, order=24):
    iv.dps=dps
    zero=iv.mpf(0)
    R=iv.mpf('1.04440033'); theta=iv.mpf(4)/7-iv.mpf('.000001')
    q=list(map(iv.mpf,'1 -2.27043254 .304358115 .16793368 4.34152016 -5.3105844 1.7701948'.split()))
    profiles=[(0,list(map(iv.mpf,'0 -.30528514 2.50038954 -1.12177152 -.07333288'.split()))),
              (2,list(map(iv.mpf,'0 1.89779072 .56594804 .07023055'.split())))]
    D=len(q)-1
    fact=math.factorial
    def plus(poly,d,x):poly[d]=poly.get(d,zero)+x
    def fs(P,e,A):
        out=[{} for _ in q];bounds=[zero for _ in q];errors=[zero for _ in q]
        C=sum(map(abs,P),zero)
        if e>=0:
            for d,p in enumerate(P):
                plus(out[0],d,p/theta**d*(A if e==1 else 1))
                if e==1:
                    plus(out[1],d,p/theta**d)
                    if d:plus(out[0],d-1,d*p/theta**d)
            bounds[0]=C if e==0 else C*abs(A)+sum((d*abs(p) for d,p in enumerate(P)),zero)/theta
            if e==1:bounds[1]=C
        else:
            k=-e
            # exp(|A| theta)<3 since |A| theta<1.
            assert (abs(A)*theta).b < 1
            for a in range(D+1):
                bounds[a]=3*C*theta**(k+a)/(fact(a)*fact(k-1)*(k+a))
                errors[a]=bounds[a]*(abs(A)*theta)**(order+1)/fact(order+1)
                for d,p in enumerate(P):
                    for j in range(order+1):
                        plus(out[a],d+k+a+j,p/theta**d*(-1)**a*(-A)**j
                             *fact(k+a+j-1)*fact(d)
                             /(fact(a)*fact(k-1)*fact(j)*fact(d+k+a+j)))
        return out,bounds,errors
    total=zero;tail=zero
    for sign in (-1,1):
        A=sign*R
        op=[q[i]*(-1)**i*fact(i) for i in range(D+1)] if sign<0 else [fact(i)*sum((q[j]*math.comb(j,i) for j in range(i,D+1)),zero) for i in range(D+1)]
        W=[[sum((op[a]*op[b]*(-1)**(a+b-i-j)*math.comb(a+b-i-j,a-i)/(2*A)**(a+b-i-j+1)
                 for a in range(i,D+1) for b in range(j,D+1)),zero) for j in range(D+1)] for i in range(D+1)]
        caches=[{e:fs(P,e,A) for e in range(1-l,2)} for l,P in profiles]
        factor=iv.exp(2*R) if sign>0 else iv.mpf(1)
        for i,(l,P) in enumerate(profiles):
            for j,(m,G) in enumerate(profiles):
                if j<i:continue
                symmetry=1 if i==j else 2
                # Cache polynomial contractions; same exponents recur in pole expansion.
                contractions={}
                for k in range(min(l,m)+1):
                    for r in range(l-k+1):
                        for t in range(m-k+1):
                            n=1+2*k+r+t;ef=1-l+k+r;eg=1-m+k+t
                            key=(ef,eg)
                            if key not in contractions:
                                f,Bf,Ef=caches[i][ef];g,Bg,Eg=caches[j][eg]
                                poly={};err=zero
                                for a in range(D+1):
                                    wg={}
                                    for b in range(D+1):
                                        for dd,vv in g[b].items():plus(wg,dd,W[a][b]*vv)
                                        err+=abs(W[a][b])*(Ef[a]*Bg[b]+Eg[b]*Bf[a]+Ef[a]*Eg[b])
                                    for da,va in f[a].items():
                                        for db,vb in wg.items():plus(poly,da+db,va*vb)
                                contractions[key]=(poly,err)
                            poly,err=contractions[key]
                            cf=math.comb(l,k)*fact(m)//fact(m-k)*math.comb(l-k,r)*math.comb(m-k,t)*(-1)**(l+m+r+t)
                            normal=symmetry*factor/theta**(l+m)
                            total+=normal*cf*sum((v*theta**(d+n)*fact(d)/fact(d+n) for d,v in poly.items()),zero)
                            tail+=abs(normal*cf)*err*theta**n/fact(n)
    result=total+iv.mpf([-1,1])*tail
    target=iv.exp(R*(1-iv.mpf('.8845')))
    assert result.b < target.a
    return result,tail,target


if __name__=='__main__':
    value,tail,target=enclosure()
    print('M enclosure:',value)
    print('analytic Taylor tail:',tail)
    print('88.45 percent threshold:',target)

