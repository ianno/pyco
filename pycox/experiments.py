'''
generic set of experiments
'''
from z3 import *

if __name__ == '__main__':
    fp = Fixedpoint()
    fp.set(engine='datalog')

    s = BitVecSort(3)
    edge = Function('edge', s, s, BoolSort())
    path = Function('path', s, s, BoolSort())
    a = Const('a',s)
    b = Const('b',s)
    c = Const('c',s)

    fp.register_relation(path,edge)
    fp.declare_var(a,b,c)
    fp.rule(path(a,b), edge(a,b))
    fp.rule(path(a,c), [edge(a,b),path(b,c)])

    v1 = BitVecVal(1,s)
    v2 = BitVecVal(2,s)
    v3 = BitVecVal(3,s)
    v4 = BitVecVal(4,s)

    fp.fact(edge(v1,v2))
    fp.fact(edge(v1,v3))
    fp.fact(edge(v2,v4))

    print "current set of rules", fp


    print fp.query(path(v1,v4)), "yes we can reach v4 from v1"

    print fp.query(path(v3,v4)), "no we cannot reach v4 from v3"
    

    #name = Datatype('name')
    #name.declare('inst', ('code', IntSort()))
    #name.declare('b', ('code', IntSort()))
    #name.declare('c', ('code', IntSort()))

    #name = name.create()

    name = BitVecSort(3)

    bname = Datatype('bname')
    bname.declare('q', ('a', name), ('b', name))
    bname.declare('w', ('a', name), ('b', name))
    bname.declare('e', ('a', name), ('b', name))
    bname = bname.create()

    #match = Datatype('match')
    #match.declare('cons', ('a', name), ('b', name))
    #match = match.create()

    match = Function('match', name, name, BoolSort())
    #mapp = Function('mapp', match, match, match)
    ref = Function('ref', bname, name, name, bname, name, name, BoolSort())
    x = Const('x', name)
    y = Const('y', name)
    w = Const('w', name)

    t = Const('t', name)
    h = Const('h', name)
    u = Const('u', name)
    j = Const('j', name)
    p = Const('p', name)
    l = Const('l', name)

    qq = Const('qq', bname)
    ww = Const('ww', bname)
    ee = Const('ee', bname)

    ff = Fixedpoint()
    ff.set(engine='datalog')

    ff.register_relation(match, ref)
    ff.declare_var(x,y,w,t,h,u,j,p,l,qq,ww,ee)

    ff.rule(match(x,w), [match(x,y), match(y,w)])
    ff.rule(ref(qq,t,h,ww,u,j), [ref(qq,t,h,ee,p,l), ref(ee,p,l,ww,u,j), match(t,u), match(h,j)])


    #a = name.inst(1)
    #b = name.inst(2)
    #c = name.inst(3)

    a = BitVecVal(1,name)
    b = BitVecVal(2,name)
    c = BitVecVal(3,name)

    q =bname.q(a,b)
    w =bname.w(b,c)
    e = bname.e(c,a)
    ff.fact(match(a,c))
    ff.fact(match(b,a))
    ff.fact(ref(q,a,b,w,b,c))
    ff.fact(ref(w,b,c,e,c,a))
    print ff
    print ff.query(match(a,c))
    print ff.query(ref(q,a,b,e,c,a))
