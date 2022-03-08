"""
Use MIP models to:
- find optimal parameters for fixed proof annotations
- search optimal proof annotations 
"""

import gurobipy as gp
from gurobipy import GRB


EPS = 0.00000001

def best_param(proof, c_lb, c_ub, tol=0.001, verbose=False):
    """
    Find the best possible speedup params so that the annotation `proof`
    leads to a contradiction
    """

    k = len(proof)
    try:
        env = gp.Env(empty=True)
        env.setParam('OutputFlag', 0)
        env.start()
        m = gp.Model(env=env)
        a = m.addVars(k+1, k+1, name='a') # The first row of a is unused except the first var,
                                                  # which represents the runtime of the initial class
        x = m.addVars(k+1, name='x') # params for speedups

        """
        Speedup rule w.p. x:
        (Q_l n^a_l) NDEPTH[a log n] subseteq (Q_l n^max(a_l,x/2)) (Q_{l+1} n^a_l) NDEPTH[(a-x) log n]

        Slowdown Rule:
        (Q_{l-1} n^a_{l-1}) (Q_l n^a_l) NDEPTH[a log n] 
        ((( subseteq (Q_{l-1} n^a_{l-1}) (Q_l n^a_l) TS[n^a]  )))
            subseteq (Q_{l-1} n^a_{l-1}) NDEPTH[c.max(a, a_l, a_{l-1})] 
        """

        # Apply the first speedup
        m.addConstr(a[1, 0] >=  x[1]/2) 
        m.addConstr(a[1, 0] >=  1) 
        # m.addConstr(a[1, 1] >=  x[1]/2)
        m.addConstr(a[1, 1] >=  1)
        m.addConstr(a[1, 2] >=  a[0,0] - x[1])
        l = 1

        # First, build the model without the constraints including `c`
        # Annotation 1 = speedup, 0 = slowdown
        for i in range(1, k):
            r_type = proof[i]
            if r_type == '0': # slowdown
                m.addConstrs(a[i+1, j] == a[i, j] for j in range(l))
                l -= 1
            elif r_type == '1': # speedup
                m.addConstrs(a[i+1, j] == a[i, j] for j in range(l))
                m.addConstr(a[i+1, l] >= a[i, l])
                m.addConstr(a[i+1, l] >= x[i+1]/2)
                m.addConstr(a[i+1, l+1] >= a[i, l])
                # m.addConstr(a[i+1, l+1] >= x[i+1]/2) # WE DO NOT NEED TO BE LARGER THAN X, THIS IS A LOGN QUANTIFIER
                m.addConstr(a[i+1, l+2] == a[i, l+1] - x[i+1])
                l += 1
            else:
                print(f'Incorrect rule type: {r_type}')
                exit(1)

        m.addConstr(a[k,0] <= a[0,0] - EPS)
        # Binary search for best c:
        best = 0
        best_a = 0
        bestp = ''
        while c_ub - c_lb > tol:
            mid = (c_ub + c_lb)/2
            if is_feasible(m, proof, a, mid):
                c_lb = mid
                if mid > best:
                    best = mid
                    best_a = a[0, 0].x
                    bestp = [x[i].x for i in range(0, k+1)]
                    if verbose:
                        pretty_print_sol(proof, a, x, mid)
            else:
                c_ub = mid

        return best, proof, bestp, best_a
    except gp.GurobiError as e:
        print('Error code ' + str(e.errno) + ': ' + str(e))

    except AttributeError:
        print('Encountered an attribute error')


def is_feasible(m, proof, a, c):
    k = len(proof)
    l = 1
    c_constr = []
    # Add the constraints with `c`
    for i in range(1, k):
        r_type = proof[i]
        if r_type == '0': # slowdown
            c_constr.append(m.addConstr(a[i+1, l] >= c*a[i, l+1]))
            c_constr.append(m.addConstr(a[i+1, l] >= c*a[i, l]))
            if l > 0:
                c_constr.append(m.addConstr(a[i+1, l] >= c*a[i, l-1]))
            l -= 1
        elif r_type == '1': # speedup
            l += 1

    m.optimize()
    res = m.status == GRB.OPTIMAL
    m.remove(c_constr)

    return res


def pretty_print_sol(proof, a, x, c):
    k = len(proof)
    print('-----------------------------')
    print(f'Found: SAT is not in Nand-depth[{c} log n]')
    print(f'Annotation: {proof}')
    print()
    print(f'Nand-depth[{a[0,0].x:.5f} log n]')
    l = 1
    print(f'\\subseteq (E n^{a[1,0].x:.5f}) (A n^{a[1,1].x:.5f}) Nand-depth[{a[1,2].x:.5f} log n]  (param {x[1].x:.5f})')
    for i in range(1, k):
        r_type = proof[i]
        if r_type == '0': # slowdown
            l -= 1
        elif r_type == '1': # speedup
            l += 1
        else:
            print(f'Incorrect rule type: {r_type}')
            exit(1)
        s = '\\subseteq ' \
            + ' '.join((f'({"E" if j%2 == 0 else "A"} n^{a[i+1,j].x:.5f})' for j in range(l+1))) \
            + f' Nand-depth[{a[i+1,l+1].x:.5f} log n]'
        print(s + (f'  (param {x[i+1].x:.5f})' if r_type == '1' else ''))
    print('-----------------------------')


def best_proof(k, c_lb=1.0, c_ub=5.0, tol=0.001, verbose=False):
    """
    Finds the best possible c for proofs of length 2k+1
    """
    k = 2*k+1
    try:
        env = gp.Env(empty=True)
        env.setParam('OutputFlag', 0)
        env.start()
        m = gp.Model(env=env)
        nl = k+1 # number of lines
        nc = k+1 # number of columns
        su = m.addVars(nl, nc, lb=1.0, name='su') # value of a_i after a speedup
        sd = m.addVars(nl, nc, lb=1.0, name='sd') # value of a_i after a slowdown 
        a = m.addVars(nl, nc, lb=1.0, name='a')
        x = m.addVars(nl, name='x') # params for speedups
        t = m.addVars(nl, vtype=GRB.BINARY, name='t') # type of i-th rule
        q = m.addVars(nl, nc, vtype=GRB.BINARY, name='q') # q[i,j] = 1 iff there is a quantifier at position j on line i
        h = m.addVars(nl, nc, vtype=GRB.BINARY, name='h') # h[i,j] = 1 iff at line i, we have j-1 quantifiers, 
                                                            # and runtime is in position j

        # Apply the first speedup
        m.addConstr(a[1, 0] >=  x[1]/2) 
        m.addConstr(a[1, 0] >=  1) 
        # m.addConstr(a[1, 1] >=  x[1]/2)
        m.addConstr(a[1, 1] >=  1)
        m.addConstr(a[1, 2] >=  a[0,0] - x[1])
        m.addConstr(q[1,0] == 1)
        m.addConstr(q[1,1] == 1)
        m.addConstrs(q[1,j] == 0 for j in range(2, k+1))
        m.addConstr(t[1] == 1)
        
        # Put constraints on h:
        m.addConstrs(h[i, j] == q[i, j-1] - q[i, j] for j in range(1, k+1) for i in range(1, nl))
        m.addConstrs(h[i, 0] == 1 - q[i, 0] for i in range(1, nl))

        ### Compute values of su, sd
        # Useful tool: "Overloaded operator" : cond >> ("implies") constraint
        # i) Speedup:
        #   Copy previous quantifiers
        m.addConstrs((q[i-1, j] == 1) >> (su[i, j] >= a[i-1, j]) for j in range(nc) for i in range(2, nl))
        #   Set speedup arg "max(x/2, a)"
        m.addConstrs((h[i, j+2] == 1) >> (su[i, j] >= x[i]/2) for j in range(nc-2) for i in range(2, nl)) 
        m.addConstrs((h[i, j+1] == 1) >> (su[i, j] >= a[i-1, j-1]) for j in range(1,nc-1)   for i in range(2, nl)) 
        # m.addConstrs((h[i, j+1] == 1) >> (su[i, j] >= x[i]/2) for j in range(nc-1)   for i in range(2, nl)) 
        #   Set runtime
        m.addConstrs((h[i, j] == 1) >> (su[i, j] == a[i-1, j-1] - x[i]) for j in range(1, nc) for i in range(2, nl)) 
 
        # ii) Slowdown:
        #   Copy l-1 quantifiers
        m.addConstrs((q[i-1, j+1] == 1) >> (sd[i, j] >= a[i-1, j]) for j in range(nc-1) for i in range(2, nl))
        #   Set runtime. We wrap this into a function.
        def set_c_constraints(c):
            cx = []
            tmp = m.addConstrs((h[i, j] == 1) >> (sd[i, j] >= c*a[i-1, j+1])  for j in range(nc-1)     for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            tmp = m.addConstrs((h[i, j] == 1) >> (sd[i, j] >= c*a[i-1, j])    for j in range(nc)   for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            tmp = m.addConstrs((h[i, j] == 1) >> (sd[i, j] >= c*a[i-1, j-1])  for j in range(1,nc) for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            return cx

        # iii) Compute value of a depending on t
        m.addConstrs((t[i] == 1) >> (a[i, j] == su[i, j]) for j in range(nc) for i in range(2, nl))
        m.addConstrs((t[i] == 0) >> (a[i, j] == sd[i, j]) for j in range(nc) for i in range(2, nl))

        # iv) Compute value of q depending on t
        m.addConstrs((t[i] == 1) >> (q[i, j] == q[i-1, j-1]) for j in range(1,nc) for i in range(2, nl))
        m.addConstrs((t[i] == 0) >> (q[i, j] == q[i-1, j+1]) for j in range(nc-1) for i in range(2, nl))
        
        # v) Ensure well-formed proof
        m.addConstrs(q[i, 0] == 1 for i in range(nl-1))
        m.addConstr(q[nl-1, 0] == 0)
        m.addConstr(h[nl-1, 0] == 1)

        m.addConstr(a[nl-1, 0] <= a[0,0] - EPS)


        def feasible(c):
            c_constr = set_c_constraints(c)
            m.optimize()
            res = m.status == GRB.OPTIMAL
            m.remove(c_constr)
            return res

        #### Binary search to find optimal value of c
        best = 1.0
        bestann = ''
        best_a = 0
        bestp = ''
        while c_ub - c_lb > tol:
            mid = (c_ub + c_lb)/2
            if feasible(mid):
                c_lb = mid
                if mid > best:
                    best = mid
                    bestann = ''.join(map(str, (int(t[i].x) for i in range(1, nl))))
                    best_a = a[0, 0].x
                    bestp = [x[i].x for i in range(0, nl)]
                    if verbose:
                        pretty_print(t, a, q, h, x, mid, k, nl, nc, verbose)
            else:
                c_ub = mid
                print(f'Value {mid} not feasible')

        return best, bestann, bestp, best_a
    except gp.GurobiError as e:
        print('Error code ' + str(e.errno) + ': ' + str(e))

    except AttributeError:
        print('Encountered an attribute error')


def pretty_print(t, a, q, h, x, c, k, nl, nc, debug=False):
    print('-----------------------------')
    print(f'Found: SAT is not in Nand-depth[{c} log n]')
    print()
    cmp_eps = 0.0001
    if debug:
        print('q:')
        for i in range(nl):
            print(' '.join(map(str, (q[i,j].x for j in range(nc)))))
        print('h:')
        for i in range(nl):
            print(' '.join(map(str, (h[i,j].x for j in range(nc)))))
        print('a:')
        for i in range(nl):
            print(' '.join(map(str, (a[i,j].x for j in range(nc)))))
        print()

    print('Annotation: ' + ''.join(map(str, (int(t[i].x) for i in range(1, nl)))))
    print()

    print(f'Nand-depth[{a[0, 0].x} log n]')
    for i in range(1, nl):
        s = ('\\subseteq ' if i > 0 else '')
        j = 0
        while q[i, j].x == 1:
            s += f'({"E" if j%2 == 0 else "A"} n^{a[i,j].x:.5f})'
            j += 1
        s += f' Nand-depth[{a[i, j].x} log n]'
        # assert abs(h[i, j].x - 1) < cmp_eps
        print(s + (f'  (param {x[i].x:.5f})' if t[i].x == 1 else ''))
    print('-----------------------------')

def dyck(n):
    if n == 0:
        yield ''
        return
    for i in range(1,n+1): # choose a number of 'up' steps before reaching 0 for the 1st time
        for p1 in dyck(i-1):
            for p2 in dyck(n-i):
                yield '1'+p1+'0'+p2

def enumerate_annotations(n):
    for p in dyck(n):
        yield p + '0'

def print_anno(q, r, x=None):
    s = '\\subseteq ' \
        + ' '.join(f'({"E" if i%2 == 0 else "A"} n^{q[i]:.5f})' for i in range(len(q))) \
        + f' Nand-depth[{r} log n]'
    if x is not None:
        s += f'   (param {x:.5f})'
    print(s)

def run_proof(annotation, params, p0, c):
    k = len(annotation)
    print('----------------')
    print(f'Running proof for {c} with annotation {annotation}')
    print(f'Parameters: {params}')
    print()
    print(f'Nand-depth[{p0} log n]')
    x = params[1]
    q = [x/2, 1]
    r = p0 - x
    print_anno(q, r, x)
    for i in range(1, k):
        if annotation[i] == '1':
            x = params[i+1]
            q.append(q[-1])
            q[-2] = max(q[-2], x/2)
            r = r - x
            print_anno(q, r, x)
        elif annotation[i] == '0':
            r = c*max(r, q[-1], q[-2]) if len(q) > 1 else c*max(r, q[-1])
            q.pop()
            print_anno(q, r)
        else:
            print('Incorrect annotation')
            exit(0)


from time import time

if __name__ == '__main__':
    s = 8

    t = time()
    r, ba1, par, a0 = best_proof(s, c_lb=2, c_ub=4.0, verbose=False)
    t2 = time()
    print(f'Best r found: {r:.5f} in {(t2-t):.5f}s for annotation {ba1}')
    r1 = best_param(ba1, 2, 4, verbose=False)
    print('Should be', r1)
    run_proof(ba1, par, a0, r)

    lb, ub = 2.0, 4.0
    best = 0
    best_annotation = ''
    best_a = 0
    t = time()
    for p in enumerate_annotations(s):
        r, z, par, a0 = best_param(p, lb, ub)
        if r > best:
            best_annotation = p
            b_par = par
            best = r
            best_a = a0
            print(f'New best found: {best:.5f} for annotation {best_annotation}')
    t2 = time()
    print(f'Best r found: {best:.5f} in {(t2-t):.5f}s for annotation {best_annotation}')
    print('Should be', best_param(best_annotation, 2, 4))
    run_proof(best_annotation, b_par, best_a, best)

