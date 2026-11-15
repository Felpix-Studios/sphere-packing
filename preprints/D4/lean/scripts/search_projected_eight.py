from pathlib import Path
import json
import numpy as np
from scipy.optimize import linprog
from scipy.special import eval_legendre
s=223/735
x=np.linspace(-1,s,8001)
A=np.array([eval_legendre(k,x) for k in range(1,33)]).T
r=linprog(np.ones(32),A_ub=A,b_ub=-np.ones(len(x)),bounds=(0,None),method='highs',options={'threads':1})
out={'status':str(r.message),'sampled_objective':float(r.fun+1) if r.success else None,'cutoff':'223/735','degree':32,'grid_points':len(x),'scope':'Numerical certificate-search diagnostic only, not a spherical bound or proof','coefficients':[1.]+r.x.tolist() if r.success else None}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='coefficients'})
