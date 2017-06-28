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
   


    c=Int('c')
    t=Int('t')

    def f(x):
        return x*t + c

    # data is a list of pairs (x, r)
    def find(data):
        s=Solver()
        s.add([ f(x) == r for (x, r) in data ])
        t = s.check()
        if s.check() == sat:
            print s.model()
        else:
            print t

    find([(1, 55)])
    find([(1, 55), (12, 34)])
    find([(1, 55), (12, 34), (13, 300)])

    name = Datatype('name')
    name.declare('a')
    name.declare('b')
    name.declare('c')
    name.declare('q')
    name.declare('w')
    name.declare('e')

    name = name.create()

    name_list = z3.Datatype('name_list')
    name_list.declare('node', ('elem', name), ('tail', name_list))
    name_list.declare('bottom')
    name_list = name_list.create()

    pair_list = z3.Datatype('pair_list')
    pair_list.declare('node', ('a', name), ('b', name),('tail', pair_list))
    pair_list.declare('bottom')
    pair_list = pair_list.create()



    bname = Datatype('bname')
    bname.declare('cons', ('name', name), ('ports', name_list))
    bname = bname.create()

    mapping = Datatype('mapping')
    mapping.declare('cons', ('pairs', pair_list))
    mapping = mapping.create()


    #we want:
    #mapping propagation and equivalence
    #refinement inference, given two names and a mapping

    #match = Datatype('match')
    #match.declare('cons', ('a', name), ('b', name))
    #match = match.create()
    is_in = Function('is_in', name, name_list, BoolSort())
    match = Function('match', mapping, mapping, mapping)
    #mapp = Function('mapp', match, match, match)
    ref = Function('ref', bname, bname, mapping, BoolSort())
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

    pp = Const('pp', name)
    pp2 = Const('pp2', name)
    ll = Const('ll', name_list)
    ll2 = Const('ll2', name_list)
    
    pl = Const('pl', pair_list)
    pl1 = Const('pl1', pair_list)

    #qq = bname.q(t,h)

    ff = Fixedpoint()
    #ff.set(engine='datalog')
    ff.set(generate_explanations=True)

    ff.register_relation(match, ref, is_in)
    ff.declare_var(x,y,w,t,h,u,j,p,l,qq,ww,ee)
    print simplify(name_list.is_bottom(ll))
    print simplify(name_list.elem(ll))


    ff.rule(ma)

    #ff.rule(is_in(pp,ll), [not simplify(name_list.is_bottom(ll)), is_in(pp, name_list.tail(ll))])
    #ff.rule(is_in(pp,ll), [name_list.node(pp, ll2)==ll])
    #ff.rule(is_in(pp,ll), [name_list.node(pp2, ll2)==ll, is_in(pp, ll2)])
    #ff.rule(match(x,w), match(w,x))
    #ff.rule(match(x,w), [match(x,y), match(y,w)])
    ff.rule(ref(qq,ww), [ref(qq,ee),
                         ref(ee,ww),
                         Implies(And(And(match(t,h),
                                         is_in(t,bname.ports(qq)),
                                         is_in(h, bname.ports(ee))),
                                     And(is_in(u, bname.ports(ww)),
                                         match(h,u))),
                                 match(t,u))
                        ])


    a = name.a
    b = name.b
    c = name.c
    q = name.q
    w = name.w
    e = name.e

    l1 = name_list.bottom
    l1 = name_list.node(a, l1)
    l1 = name_list.node(b, l1)

    l2 = name_list.bottom
    l2 = name_list.node(b, l2)
    l2 = name_list.node(c, l2)

    l3 = name_list.bottom
    l3 = name_list.node(c, l3)
    l3 = name_list.node(a, l3)

    print simplify(name_list.elem(l3))
    q =bname.cons(q, l1)
    w =bname.cons(w,l2)
    e = bname.cons(e,l3)
    ff.fact(match(c,a))
    ff.fact(ref(q,w))
    print ff
    print ff.query(ref(q,e))
    ff.fact(ref(w,e))
    print ff.query(ref(q,e))
    ff.fact(match(b,a))
    print ff.query(ref(q,e))
    print ff.get_answer()
