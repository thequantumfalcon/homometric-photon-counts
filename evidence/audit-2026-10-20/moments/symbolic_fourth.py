"""Certify all-t moment identities by exact evaluation plus degree bounds."""
from fractions import Fraction
from pathlib import Path
import contextlib
import hashlib
import io
import json
import time
from reconstruct import Engine


class PolynomialEvaluationEngine(Engine):
    def __init__(self, t):
        super().__init__(4)
        self.t = Fraction(t)
        self.scale = 240*self.lcm*self.t.denominator**self.p

    def site(self, w, radical):
        # Incoming w=120*z; scale by 240 to absorb every sixth-root rotation.
        w = tuple(2*c for c in w)
        powers = [(1,0,0,0)]
        for k in range(self.p):
            powers.append(self.field_multiply(powers[-1],w,radical))
        parts = [self.zero() for _ in range(4)]
        for b in range(self.n):
            for a in range(self.n):
                d,degree = a-b,a+b
                coeff = powers[abs(d)]
                if d < 0:
                    coeff = (coeff[0],-coeff[1],coeff[2],-coeff[3])
                factor = (240**(degree-abs(d))*self.lcm**degree
                          // (self.factorials[a]*self.factorials[b]))
                factor *= self.t.numerator**(d*d)
                factor *= self.t.denominator**(self.p*degree-d*d)
                for k in range(4):
                    parts[k][b*self.n+a] = coeff[k]*factor
        return parts


def main():
    start = time.monotonic()
    records = []
    # All nodes are strictly positive: t=0 would create zero polynomial parts
    # and is unnecessary. t>1 is a formal polynomial evaluation, not a model.
    for node in range(1,34):
        engine = PolynomialEvaluationEngine(node)
        with contextlib.redirect_stdout(io.StringIO()):
            moments = engine.run()
        deltas = [Fraction(moments['A'][str(k)])-Fraction(moments['B'][str(k)]) for k in range(5)]
        target = Fraction(455015761,20000)*node**8*(1-node**2)**5*(node**6+3*node**4+6*node**2+6)
        assert deltas[:4] == [0]*4
        assert deltas[4] == target
        records.append(dict(t=node, differences=[str(v) for v in deltas], target=str(target)))
        print(f'Exact polynomial node {node}/33 passed', flush=True)
    result = dict(all_passed=True, nodes=records,
                  moment_degree_bounds={str(k): 2*k*k for k in range(5)},
                  identity='D4(t)=455015761/20000*t^8*(1-t^2)^5*(t^6+3*t^4+6*t^2+6)',
                  conclusion='D1=D2=D3=0 identically; D4>0 for every 0<t<1',
                  seconds=time.monotonic()-start,
                  engine_sha256=hashlib.sha256(Path(__file__).with_name('reconstruct.py').read_bytes()).hexdigest(),
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(__file__).with_name('symbolic_fourth.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: all-t identities certified by 33 nodes and degree bound 32, {result["seconds"]:.2f}s')


if __name__ == '__main__':
    main()
