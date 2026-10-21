"""Read-only exact consistency and dependency checks of higher moment tables.

These checks supplement the generating-function proof; they do not regenerate
moments or establish that moment inequalities characterize the target law.
"""
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import sys


def main():
    sys.set_int_max_str_digits(0)
    here=Path(__file__).resolve().parent
    root=here.parents[1]
    sealed=root/'audit-2026-10-20/moments/reconstructed_order_32.json'
    previous=json.loads(sealed.read_text())['moments']
    reports=[]
    for order in (64,96):
        path=here/f'fixed_t_moments_order_{order}.json'
        if not path.exists():
            if order==64:raise ValueError('Required order64 table missing')
            continue
        saved=json.loads(path.read_text())
        if saved['maximum_moment']!=order:raise ValueError('Wrong moment order')
        table={g:{int(k):Q(v) for k,v in t.items()} for g,t in saved['moments'].items()}
        if set(table)!={'A','B'}:raise ValueError('Wrong structures')
        comparisons=0
        for g,t in table.items():
            if set(t)!=set(range(order+1)) or t[0]!=1:raise ValueError('Incomplete or unnormalized table')
            for k,v in previous[g].items():
                if t[int(k)]!=Q(v):raise ValueError('Prefix mismatch')
                comparisons+=1
            if any(v<=0 for v in t.values()):raise ValueError('Nonpositive moment')
            if any(t[k+1]>3969*t[k] for k in range(order)):raise ValueError('Support bound failed')
            if any(t[k]**2>t[k-1]*t[k+1] for k in range(1,order)):raise ValueError('Log-convexity failed')
        checked=[]
        for original,digest in saved['dependencies'].items():
            normalized=original.replace('\\','/')
            matches=[marker for marker in ('/audit-2026-10-20/','/continuation-2026-10-20/') if marker in normalized]
            if len(matches)!=1:raise ValueError('Unexpected dependency path')
            marker=matches[0]
            relative=marker[1:]+normalized.split(marker,1)[1]
            dependency=root/relative
            if sha256(dependency.read_bytes()).hexdigest()!=digest:
                raise ValueError('Producer dependency changed: '+relative)
            checked.append(relative)
        reports.append({'order':order,'sha256':sha256(path.read_bytes()).hexdigest(),
                        'exact_prefix_comparisons':comparisons,'checked_dependencies':checked})
        previous=saved['moments']
    print(json.dumps({'status':'PASS','tables':reports,
        'scope':'Exact nested-prefix, normalization, positivity, support, log-convexity and source dependency checks; not a fresh reconstruction.'},indent=2))


if __name__=='__main__':main()
