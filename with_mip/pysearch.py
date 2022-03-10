"""
This file contains functions that, given a `k`, search for the proof `p`
that yiels the largest `c` that leads to a contradiction using this proof.
"""
import gurobipy as gp
from gurobipy import GRB

EPS = 0.00000001

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
        nc = k//2+1+2 # number of columns
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
        m.addConstrs(q[1,j] == 0 for j in range(2, nc))
        m.addConstr(t[1] == 1)
        
        # Put constraints on h:
        m.addConstrs(h[i, j] == q[i, j-1] - q[i, j] for j in range(1, nc) for i in range(1, nl))
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
        best_c = 1.0
        best_proof = ''
        best_x = ''
        best_r = 0
        while c_ub - c_lb > tol:
            mid = (c_ub + c_lb)/2
            if feasible(mid):
                c_lb = mid
                if mid > best_c:
                    best_c = mid
                    best_proof = ''.join(map(str, (int(t[i].x) for i in range(1, nl))))
                    best_x = [x[i].x for i in range(0, nl)]
                    best_r = a[0, 0].x
                    if verbose:
                        print(f'Value {mid} feasible')
                        pretty_print(t, a, q, h, x, mid, k, nl, nc, verbose)
            else:
                c_ub = mid
                if verbose:
                    print(f'Value {mid} not feasible')

        return best_c, best_proof, best_x, best_r
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

 

def best_proof_sparse(k, c_lb=1.0, c_ub=5.0, tol=0.001, verbose=False):
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
        nc = k//2+1+5 # number of columns
        a = m.addVars(nl, nc, name='a')
        x = m.addVars(nl, name='x') # params for speedups
        r = m.addVars(nl, name='r') # runtime
        t = m.addVars(nl, vtype=GRB.BINARY, name='t') # type of i-th rule

        """
        We proceed differently: we put the last quantifier of line i in a[i, -1], 
        2nd to last in a[i, -2], etc.
        """

        # Apply the first speedup
        m.addConstr(a[1, nc-2] >=  x[1]/2) 
        m.addConstr(a[1, nc-2] >=  1) 
        m.addConstr(a[1, nc-1] >=  1)
        m.addConstr(r[1] ==  r[0] - x[1])
        m.addConstr(t[1] == 1)
        
        ### Compute values of su, sd
        # Useful tool: "Overloaded operator" : cond >> ("implies") constraint
        # i) Speedup:
        #   Copy previous quantifiers
        m.addConstrs((t[i] == 1) >> (a[i, j] >= a[i-1, j+1]) for j in range(nc-1) for i in range(2, nl))
        #   Set speedup arg "max(x/2, a)"
        m.addConstrs((t[i] == 1) >> (a[i, nc-2] >= x[i]/2)       for i in range(2, nl)) 
        m.addConstrs((t[i] == 1) >> (a[i, nc-1] >= a[i-1, nc-1]) for i in range(2, nl)) 
        #   Set runtime
        m.addConstrs((t[i] == 1) >> (r[i] == r[i-1] - x[i]) for j in range(1, nc) for i in range(2, nl)) 
 
        # ii) Slowdown:
        #   Copy l-1 quantifiers
        m.addConstrs((t[i] == 0) >> (a[i, j] == a[i-1, j-1]) for j in range(1, nc) for i in range(2, nl))
        #   Set runtime. We wrap this into a function.
        def set_c_constraints(c):
            cx = []
            tmp = m.addConstrs((t[i] == 0) >> (r[i] >= c*r[i-1])  for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            tmp = m.addConstrs((t[i] == 0) >> (r[i] >= c*a[i-1, nc-1]) for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            tmp = m.addConstrs((t[i] == 0) >> (r[i] >= c*a[i-1, nc-2]) for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            return cx
        
        # iii) Ensure well-formed proof
        m.addConstrs(sum(t[j] for j in range(1, i)) >= (i)//2 for i in range(2, nl-1))
        m.addConstr(t.sum() == k//2)

        # iv) Require contradiction
        m.addConstr(r[nl-1] <= r[0] - EPS)


        def feasible(c):
            c_constr = set_c_constraints(c)
            m.optimize()
            res = m.status == GRB.OPTIMAL
            m.remove(c_constr)
            return res

        #### Binary search to find optimal value of c
        best_c = 1.0
        best_proof = ''
        best_x = ''
        best_r = 0
        while c_ub - c_lb > tol:
            mid = (c_ub + c_lb)/2
            if feasible(mid):
                c_lb = mid
                if mid > best_c:
                    best_c = mid
                    best_proof = ''.join(map(str, (int(t[i].x) for i in range(1, nl))))
                    best_x = [x[i].x for i in range(0, nl)]
                    best_r = r[0].x
                    if verbose:
                        print(f'Value {mid} feasible')
                        # pretty_print(t, a, q, h, x, mid, k, nl, nc, verbose)
            else:
                c_ub = mid
                if verbose:
                    print(f'Value {mid} not feasible')

        return best_c, best_proof, best_x, best_r
    except gp.GurobiError as e:
        print('Error code ' + str(e.errno) + ': ' + str(e))

    except AttributeError:
        print('Encountered an attribute error')
