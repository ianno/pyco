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
    

    name = Datatype('name')
    name.declare('a')
    name.declare('b')
    name.declare('c')
    name.declare('q')
    name.declare('w')
    name.declare('e')

    name = name.create()

    bname = Datatype('bname')
    bname.declare('cons', ('name', name), ('a', name), ('b', name))
    bname = bname.create()

    #match = Datatype('match')
    #match.declare('cons', ('a', name), ('b', name))
    #match = match.create()
    
    match = Function('match', name, name, BoolSort())
    #mapp = Function('mapp', match, match, match)
    ref = Function('ref', bname, bname, BoolSort())
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

    #qq = bname.q(t,h)

    ff = Fixedpoint()
    #ff.set(engine='datalog')
    ff.set(generate_explanations=True)

    ff.register_relation(match, ref)
    ff.declare_var(x,y,w,t,h,u,j,p,l,qq,ww,ee)

    ff.rule(match(x,w), match(w,x))
    ff.rule(match(x,w), [match(x,y), match(y,w)])
    ff.rule(ref(qq,ww), [ref(qq,ee), ref(ee,ww), bname.a(qq)==t, bname.b(qq)==h, bname.a(ww)==p, bname.b(ww)==l, bname.a(ee)==u, bname.b(ee)==j, match(t,p), match(h,l)])


    a = name.a
    b = name.b
    c = name.c
    q = name.q
    w = name.w
    e = name.e

    q =bname.cons(q,a,b)
    w =bname.cons(w,b,c)
    e = bname.cons(e,c,a)
    ff.fact(match(c,a))
    ff.fact(ref(q,w))
    print ff
    print ff.query(ref(q,e))
    ff.fact(ref(w,e))
    print ff.query(ref(q,e))
    ff.fact(match(b,a))
    print ff.query(ref(q,e))
    print ff.get_answer()
