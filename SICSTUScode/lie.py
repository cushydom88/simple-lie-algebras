#!/usr/bin/python3

# import dd.autoref as _bdd
import dd.cudd as _bdd
import datetime

common = {"bdd": _bdd.BDD(),
          "GL2": [[[1, 0], [1, 1]],
                  [[1, 1], [0, 1]],
                  [[1, 1], [1, 0]],
                  [[0, 1], [1, 1]],
                  [[0, 1], [1, 0]]],
          }

def vars(n):
    m = 2 ** n - 1
    elts = []
    for i in range(1,m+1):
        for j in range(1,m+1):
            if i < j:
                elts += [f'x[{i},{j}]']
    return elts

def element(i, j):
    bdd = common["bdd"]
    if i < j:
        return bdd.var(f'x[{i},{j}]')
    elif i > j:
        return bdd.var(f'x[{j},{i}]')
    else:
        return bdd.false

def oddbits(i):
    parity = 0
    while i > 0:
        parity = parity ^ (i & 1)
        i = i >> 1
    return parity == 1

def jacobiIdentity(formula, n):
    bdd = common["bdd"]
    m = 2 ** n - 1
    tally = 0
    for i1 in range(1,m+1):
        for i2 in range(1,m+1):
            for i3 in range(1,m+1):
                if i1 < i2 and i2 < i3 and i1 != (i2^i3):
                    tally += 1
    constraints = []
    for i1 in range(1,m+1):
        for i2 in range(1,m+1):
            for i3 in range(1,m+1):
                if i1 < i2 and i2 < i3 and i1 != (i2^i3):
                    i4  = (i1^i2)
                    i5  = (i1^i3)
                    i6  = (i2^i3)
                    a = element(i1,i2)
                    b = element(i3,i4)
                    c = element(i1,i3)
                    d = element(i2,i5)
                    e = element(i2,i3)
                    f = element(i1,i6)
                    constraints += [bdd.add_expr(r'({} /\ {}) ^ ({} /\ {}) ^ ({} /\ {}) ^ TRUE'.format(a,b,c,d,e,f))]
                    tally -= 1
                    print(f'did one jacobi identity, {tally} to go')
    constraint = divideAndConquerAnd(constraints)
    print(f'{datetime.datetime.now()}: formed conjunction')
    formula = bdd.apply('&', formula, constraint)
    print(f'{datetime.datetime.now()}: conjoined with formula')
    return formula

def divideAndConquerAnd(lst):
    bdd = common["bdd"]
    l = len(lst)
    if l == 0:
        return bdd.true
    elif l == 1:
        return lst[0]
    else:
        d = l // 2
        return bdd.apply('&', divideAndConquerAnd(lst[0:d]), divideAndConquerAnd(lst[d:]))
                         
def stopCertainIdeals(formula, n):
    bdd = common["bdd"]
    m = 2 ** n - 1
    for i in range(1,m+1):
        L1 = {j for j in range(1,m+1) if oddbits(i & j)}
        L0 = set(range(1,m+1)).difference(L1)
        xs = []
        for a in L0:
            xs += ['(' + ' | '.join([str(element(b,a^b)) for b in L1]) + ')']
        constraint = bdd.add_expr(' & '.join(xs))
        formula = bdd.apply('&', formula, constraint)
        print(f'{datetime.datetime.now()}: did one stop certain ideals, {m-i} to go')
    return formula            

def actFaithfully(formula, n):
    bdd = common["bdd"]
    m = 2 ** n - 1
    for i in range(1,m+1):
        L1 = {j for j in range(1,m+1) if oddbits(i & j)}
        L0 = set(range(1,m+1)).difference(L1)
        xs = []
        for a in L0:
            xs += ['(' + ' | '.join([str(element(b,a)) for b in L1]) + ')']
        constraint = bdd.add_expr(' & '.join(xs))
        formula = bdd.apply('&', formula, constraint)
        print(f'{datetime.datetime.now()}: did one act faithfully, {m-i} to go')
    return formula            
                    
def breakGL2Symmetries(formula, n):
    tally = 0
    for i in range(1,n+1):
        for j in range(i+1,n+1):
            for k in range(0,5):
                tally += 1
    for i in range(1,n+1):
        for j in range(i+1,n+1):
            for k in range(0,5):
                GL2k = common["GL2"][k]
                NbyN = addToGlnSmall(i, j, GL2k[0][0], GL2k[0][1], GL2k[1][0], GL2k[1][1], n)
                formula = breakSymmetry(makePerm(NbyN, n), formula)
                tally -= 1
                print(f'{datetime.datetime.now()}: broke one symmetry, {tally} to go')
    return formula

def addToGlnSmall(I, J, A, B, C, D, n):
    NbyN = [[     A if x == I and y == I \
             else B if x == I and y == J \
             else C if x == J and y == I \
             else D if x == J and y == J \
             else 1 if x == y            \
             else 0 \
             for y in range(1,n+1)] for x in range(1,n+1) ]
    return NbyN

def makePerm(NbyN, n):
    m = 2 ** n - 1
    return [makePermK(NbyN, n, k) for k in range(1,m+1)]

def makePermK(NbyN, n, k):
    powers = [2 ** (n-i) for i in range(1,n+1)]
    masked = [[NbyN[i][j] if (powers[j] & k)>0 else 0 for j in range(0,n)] for i in range(0,n)]
    xored = [(1 & sum(masked[i])) for i in range(0,n)]
    return sum([powers[i] * xored[i] for i in range(0,n)])

def breakSymmetry(p, formula):
    bdd = common["bdd"]
    m = len(p)
    vector = [element(i,j) for j in range(1,m+1) for i in range(1,m+1)]
    pvector = [element(p[i-1],p[j-1]) for j in range(1,m+1) for i in range(1,m+1)]
    # vectors = [f'x[{i},{j}]' for j in range(1,m+1) for i in range(1,m+1)]
    # pvectors = [f'x[{p[i-1]},{p[j-1]}]' for j in range(1,m+1) for i in range(1,m+1)]
    # print(f'lexLessEq( {vectors}\n         , {pvectors}\n         )\n')
    constraint = lexLessEq(vector, pvector)
    formula = bdd.apply('&', formula, constraint)
    return formula

def lexLessEq(vector, pvector):
    bdd = common["bdd"]
    if len(vector) == 0:
        return bdd.true
    elif vector[0] == bdd.false:
        assert pvector[0] == bdd.false, pvector[0]
        return lexLessEq(vector[1:], pvector[1:])
    else:
        x = vector[0]
        y = pvector[0]
        nx = bdd.apply('~', x)
        u = bdd.apply('&', nx, y)
        v = bdd.apply('<->', x, y)
        w = bdd.apply('&', v, lexLessEq(vector[1:], pvector[1:]))
        return bdd.apply('|', u, w)

def simpleTables(n):
    bdd = common["bdd"]
    bdd.declare(*vars(n))
    formula = bdd.true
    formula = stopCertainIdeals(formula, n)
    formula = actFaithfully(formula, n)
    formula = jacobiIdentity(formula, n)
    formula = breakGL2Symmetries(formula, n)
    return formula

