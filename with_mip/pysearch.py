"""
This file contains functions that, given a `k`, search for the proof `p`
that yiels the largest `c` that leads to a contradiction using this proof.
"""
import gurobipy as gp
from gurobipy import GRB

EPS = 0.00000001

def best_proof_sparse(k, c_lb=1.0, c_ub=5.0, tol=0.001, n_threads=10, verbose=0):
    """
    Finds the best possible c for proofs of length 2k+1
    """
    k = 2*k+1
    try:
        env = gp.Env(empty=True)
        if verbose < 2:
            env.setParam('OutputFlag', 0)
        env.start()
        m = gp.Model(env=env)
        m.Params.Threads = n_threads
        nl = k+1 # number of lines
        nc = k//2+1+5 # number of columns
        a = m.addVars(nl, nc, lb=1, name='a')
        x = m.addVars(nl, name='x') # params for speedups
        r = m.addVars(nl, name='r') # runtime
        su = m.addVars(nl, vtype=GRB.BINARY, name='su') # usual speedup
        sd  = m.addVars(nl, vtype=GRB.BINARY, name='sd')  # slowdown

        """
        We proceed differently: 
        we put the last quantifier of line i in a[i, -1], 
        2nd to last in a[i, -2], etc.
        """

        # Apply the first speedup
        m.addConstr(a[1, nc-2] >=  x[1]/2) 
        m.addConstr(r[1] ==  r[0] - x[1])
        m.addConstr(su[1] == 1)
        
        ### Compute values of su, sd
        # Useful tool: "Overloaded operator" : cond >> ("implies") constraint
        # i) Usual Speedup:
        #   Copy previous quantifiers
        m.addConstrs((su[i] == 1) >> (a[i, j] >= a[i-1, j+1]) for j in range(nc-1) for i in range(2, nl))
        #   Set speedup arg "max(x/2, a)"
        m.addConstrs((su[i] == 1) >> (a[i, nc-2] >= x[i]/2)       for i in range(2, nl)) 
        #   Set runtime
        m.addConstrs((su[i] == 1) >> (r[i] == r[i-1] - x[i]) for j in range(1, nc) for i in range(2, nl)) 
 
        # ii) Slowdown:
        # The best slowdown is always "Speedup + exhaustive search + usual slowdown"
        #       The runtime becomes TS, hence we have to use slowdown afterwards
        #       in order for the proof to be "well-typed".
        #   Copy l-1 quantifiers
        m.addConstrs((sd[i] == 1) >> (a[i, j] == a[i-1, j-1]) for j in range(1, nc) for i in range(2, nl))

        #   Set runtime. We wrap this into a function.
        def set_c_constraints(c):
            cx = []
            # Slowdown
            tmp = m.addConstrs((sd[i] == 1) >> (r[i] >= c*r[i-1]/2)  for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            tmp = m.addConstrs((sd[i] == 1) >> (r[i] >= c*a[i-1, nc-1]) for i in range(2, nl))
            cx += [tmp[x] for x in tmp]
            tmp = m.addConstrs((sd[i] == 1) >> (r[i] >= c*a[i-1, nc-2]) for i in range(2, nl))
            cx += [tmp[x] for x in tmp]

            return cx
        
        # iii) Ensure well-formed proof
        m.addConstrs(sum(su[j] - sd[j] for j in range(1, i)) >= 0 for i in range(2, nl-1))
        m.addConstr(sum(su[j] - sd[j] for j in range(1, nl)) == -1)
        #   Only one rule per line
        m.addConstrs(su[i] + sd[i] == 1 for i in range(nl))

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
                    best_proof = ''.join(map(str, (int(su[i].x) for i in range(1, nl))))
                    best_x = [x[i].x for i in range(0, nl)]
                    best_r = r[0].x
                    if verbose > 0:
                        print(f'Value {mid} feasible')
                        # debug(a, nl, nc)
            else:
                c_ub = mid
                if verbose > 0:
                    print(f'Value {mid} not feasible')

        return best_c, best_proof, best_x, best_r
    except gp.GurobiError as e:
        print('Error code ' + str(e.errno) + ': ' + str(e))

    except AttributeError:
        print('Encountered an attribute error')

def debug(a, nl, nc):
    for i in range(nl):
        print(' '.join(f'(Q n^{a[i,j].x})' for j in range(nc)))