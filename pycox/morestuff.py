from z3 import *

#component names
CBaseName, CBaseNames = EnumSort('CBaseName', ['A', 'B', 'C'])
CUniqueName, CUniqueNames = EnumSort('CUniqueName', ['A0', 'B0', 'C0'])

#list all reference names
BaseName, BaseNames = EnumSort('BaseName', ['a', 'a', 'b', 'c'])
#list all real names
UniqueName, UniqueNames = EnumSort('UniqueName', ['a0', 'a1', 'b0', 'c0'])

Port = Datatype('Port')
Port.declare('port',
             ('base_name', BaseName),
             ('unique_name', UniqueName))

Port = Port.create()

#build list according to the Tree example
PortList = Datatype('PortList')
PortList.declare('node', ('port', Port), ('port_list', PortList))
PortList.declare('bottom')

PortList = PortList.create()

Component = Datatype('Component')
Component.declare('component',
                  ('base_name', CBaseName),
                  ('unique_name', CUniqueName),
                  ('input_ports', PortList),
                  ('output_ports', PortList))

Component = Component.create()

solver = Solver()

#Z3 do not handle recursive declarations with quantifiers:(

# def port_assert_on_list(function, port_assertion, p, l):
#     return ForAll([p, l],
#              If(PortList.is_bottom(l),
#                 function(l, p) == False,
#                 If(port_assertion,
#                    function(l, p) == True,
#                    function(l, p) == function(PortList.port_list(l), p)
#                   )
#                )
#              )

#declare functions
list_has_port = Function('list_has_port', PortList, Port, BoolSort())
list_has_port_with_base_name = Function('list_has_port_with_base_name',
                             PortList,
                             BaseName,
                             BoolSort()
                            )
list_has_port_with_unique_name = Function('list_has_port_with_unique_name',
                               PortList,
                               UniqueName,
                               BoolSort()
                              )

comp_has_port_base_name = Function('comp_has_port_base_name',
                                   Component,
                                   BaseName,
                                   BoolSort())
#p = Const('p', Port)
#l = Const('l', PortList)
#c = Const('c', Component)

# solver.add( port_assert_on_list(list_has_port,
#                                 PortList.port(l) == p,
#                                 p, l)
#           )
# 
# solver.add( port_assert_on_list(list_has_port_with_base_name,
#                                 Port.base_name(PortList.port(l)) == Port.base_name(p),
#                                 p, l)
#           )
# 
# solver.add( port_assert_on_list(list_has_port_with_unique_name,
#                                 Port.unique_name(PortList.port(l)) == Port.unique_name(p),
#                                 p, l)
#           )



def define_has_port_constraints(port_list, port):
    constraints = []
    iter_list = port_list

    constraints.append(Implies(PortList.is_bottom(iter_list),
                       list_has_port(iter_list, port) == False))

    while is_false(simplify(PortList.is_bottom(iter_list))) :
        constraints.append( Implies(PortList.port(iter_list) == port,
                                    list_has_port(port_list, port) == True  ))
        constraints.append( Implies( And( Not( PortList.port(iter_list) == port ),
                                          PortList.is_bottom(PortList.port_list(iter_list))
                                        ),
                                     list_has_port(port_list, port) == False
                                    ))
        iter_list = PortList.port_list(iter_list)

    return constraints

def define_list_has_port_name_constraints(port_list, port_base_name):
    constraints = []
    iter_list = port_list

    constraints.append(Implies(PortList.is_bottom(iter_list),
                       list_has_port_with_base_name(iter_list, port_base_name) == False))
    print is_false(simplify(PortList.is_bottom(iter_list)))
    print simplify(PortList.is_bottom(iter_list))
    while is_false(simplify(PortList.is_bottom(iter_list))) :
        print '!'
        constraints.append( Implies(Port.base_name(PortList.port(iter_list)) == port_base_name,
                                    list_has_port_with_base_name(port_list, port_base_name) == True  ))
        constraints.append( Implies( And( Not( Port.base_name(PortList.port(iter_list)) == port_base_name ),
                                          PortList.is_bottom(PortList.port_list(iter_list))
                                        ),
                                     list_has_port_with_base_name(port_list, port_base_name) == False
                                    ))
        iter_list = PortList.port_list(iter_list)

    return constraints



def define_comp_has_port_name_constraints(component, port_base_name):
    constraints = []
    input_l = Component.input_ports(component)
    output_l = Component.output_ports(component)

    constraints += define_list_has_port_name_constraints(input_l, port_base_name)
    constraints += define_list_has_port_name_constraints(output_l, port_base_name)
    constraints.append( If(list_has_port_with_base_name(input_l, port_base_name),
                           comp_has_port_base_name(component, port_base_name) == True,
                           comp_has_port_base_name(component, port_base_name) == list_has_port_with_base_name(output_l, port_base_name)))
    return constraints

if __name__ == '__main__':

    #create port_list
    port_list = PortList.bottom

    port = Port.port(BaseNames[0], UniqueNames[0])

    port_list = PortList.node(port, port_list)

    port_list = PortList.node(Port.port(BaseNames[2], UniqueNames[1]), port_list)

    #print
    print port_list
   
    c1 = Component.component(CBaseNames[0], CUniqueNames[0], port_list, PortList.bottom)

    print c1

    plist = PortList.bottom

    port_2 = Port.port(BaseNames[1], UniqueNames[1])

    plist = PortList.node(port_2, plist)

    c2 = Component.component(CBaseNames[1], CUniqueNames[1], PortList.bottom, plist)

    print c2

    x = Const('x', Component)
    y = Const('y', Component)

    #let's check if we can find a A connected to B,
    #on ports a-b
    ct0 = And(Component.base_name(x) == CBaseNames[0],
              Component.base_name(y) == CBaseNames[0])
    solver.add(ct0)

    #CT0 not sufficient, otherwise solver will find a new component.
    #We have to force the solver to look among exisitng objects(can be implemented as a OR on a list)
    ct1 = Or(x == c1, x == c2)
    solver.add(ct1)

    ct2 = Or(y == c1, y == c2)
    solver.add(ct2)

    #add condition about ports
    #solver.add(define_has_port_constraints(plist, port_2))
    #solver.add(define_has_port_constraints(plist, port))

    #check condition
    #solver.add(list_has_port(plist, port_2))

    #check if component has port with name
    solver.add(define_comp_has_port_name_constraints(x, BaseNames[3]))
    solver.add(comp_has_port_base_name(x, BaseNames[3]))

    print solver.check()
    print solver.sexpr()
    print solver.model()
