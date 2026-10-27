"""Offline finite certificate for the fixed 88.45% witness. No optimization.

Run: python3 verify.py [--manifest]
Only dependency: mpmath==1.3.0. JSON goes to stdout; no files are written.
The analytic counting and PRZZ transplantation are not verified by this code.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import mpmath as mp
from numerical_interval import enclosure

ROOT = Path(__file__).resolve().parent


def exact_checks():
    q = list(map(F, '1 -2.27043254 .304358115 .16793368 4.34152016 -5.3105844 1.7701948'.split()))
    p1 = list(map(F, '0 -.30528514 2.50038954 -1.12177152 -.07333288'.split()))
    p2 = list(map(F, '0 1.89779072 .56594804 .07023055'.split()))
    r = [sum((q[j]*math.comb(j,k)*F(1,2)**(j-k)*(-1)**k
              for j in range(k,len(q))),F(0)) for k in range(len(q))]
    assert r == list(map(F,'.09491351 .997010185 2.089866 0 -2.29671034 0 1.7701948'.split()))
    assert q[0] == sum(p1) == 1 and p1[0] == p2[0] == 0 and r[1] != 0
    assert F('1.04440033')*(F(4,7)-F('0.000001')) < 1
    # Complete formal Laurent coefficient comparisons, not sampled points.
    expected = {
        (0,0): {(1,1,1):1},
        (2,0): {(1,1,3):1,(0,1,2):-2,(-1,1,1):1},
        (0,2): {(1,1,3):1,(1,0,2):-2,(1,-1,1):1},
        (2,2): {(1,1,5):7,(1,0,4):-6,(0,1,4):-6,
                (1,-1,3):1,(-1,1,3):1,(0,0,3):8,
                (-1,0,2):-2,(0,-1,2):-2,(-1,-1,1):1},
    }
    for (l,m), want in expected.items():
        got={}
        for k in range(min(l,m)+1):
            for a in range(l-k+1):
                for b in range(m-k+1):
                    key=(1-l+k+a,1-m+k+b,1+2*k+a+b)
                    c=(math.comb(l,k)*math.factorial(m)//math.factorial(m-k)
                       *math.comb(l-k,a)*math.comb(m-k,b)*(-1)**(l+m+a+b))
                    got[key]=got.get(key,0)+c
        got={key:v for key,v in got.items() if v}
        assert got==want,(l,m,got,want)
    return {'center_coefficients':[str(x) for x in r],
            'full_Laurent_kernel_identities':len(expected),
            'profile_endpoints_exact':True,'R_theta_below_one':True}


def run():
    out={'scope':'finite main-term functional only; analytic transplantation requires review',
         'mpmath_version':mp.__version__,'exact_checks':exact_checks(),'interval_runs':[]}
    midpoint22=[]
    for precision,order in ((40,20),(45,24),(55,24),(70,24)):
        mp.mp.dps=precision
        value,tail,target=enclosure(precision,order)
        lo,hi=mp.mpf(value.a),mp.mpf(value.b)
        target_lo,target_hi=mp.mpf(target.a),mp.mpf(target.b)
        assert hi < target_lo
        if order==24:
            assert mp.mpf('1.12818163807203565629105') < lo
            assert hi < mp.mpf('1.12818163807203565629124')
            assert mp.mpf(tail.b) < mp.mpf('8.799e-23')
            midpoint22.append(mp.nstr((lo+hi)/2,22))
        assert mp.mpf('1.12820541062467513417945') < target_lo
        assert target_hi < mp.mpf('1.12820541062467513417947')
        out['interval_runs'].append({
            'precision':precision,'Taylor_order':order,
            'M_interval':str(value),'Taylor_tail':str(tail),
            'threshold_interval':str(target),'strict_8845_gate':True})
    assert len(set(midpoint22))==1,midpoint22
    out['midpoint_22_digits']=midpoint22[0]
    out['precision_comparison_45_70_passed']=True
    out['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                          for name in ('numerical_interval.py','verify.py','manuscript.tex')}
    return out


def check_manifest():
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        assert '/' not in name and name not in ('.','..')
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--manifest',action='store_true')
    args=parser.parse_args()
    if args.manifest:check_manifest()
    print(json.dumps(run(),indent=2))
