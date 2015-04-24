'''
This module is a scrapebook, used for experiments.

Author: Antonio Iannopollo
'''

from z3 import *

#component names
CBaseName, CBaseNames = EnumSort('CBaseName', ['A', 'B', 'C'])
CUniqueName, CUniqueNames = EnumSort('CUniqueName', ['A0', 'B0', 'C0'])

#list all reference names
BaseName, BaseNames = EnumSort('BaseName', ['a', 'b', 'c'])
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

#Z3 does not handle recursive declarations with quantifiers:(

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
    iter_list = port_list

    while is_false(simplify(PortList.is_bottom(iter_list))) :
        if is_true(simplify(PortList.port(iter_list) == port)):
            return [list_has_port(port_list, port) == True]

        iter_list = PortList.port_list(iter_list)

    return [list_has_port(port_list, port) == False]


def define_list_has_port_name_constraints(port_list, port_base_name):

    iter_list = port_list

    while is_false(simplify(PortList.is_bottom(iter_list))) :
        if is_true(simplify(Port.base_name(PortList.port(iter_list)) == port_base_name)):
            #return [list_has_port_with_base_name(port_list, port_base_name) == True]
            return True

        iter_list = PortList.port_list(iter_list)


    #return [list_has_port_with_base_name(port_list, port_base_name) == False]
    return False




def define_comp_has_port_name_constraints(component, port_base_name):
    constraints = []
    input_l = Component.input_ports(component)
    output_l = Component.output_ports(component)

    if (define_list_has_port_name_constraints(input_l, port_base_name) or
        define_list_has_port_name_constraints(output_l, port_base_name)):
        return [comp_has_port_base_name(component, port_base_name) == True]

    return [comp_has_port_base_name(component, port_base_name) == False]


def define_comp_has_port_name_total(component_list):
    constraints = []

    for comp in component_list:
        for port_base_name in BaseNames:
            constraints += define_comp_has_port_name_constraints(comp, port_base_name)
    print constraints
    return constraints

#def derive_connection_constraints(list_of_components):
#    '''
#    Derives connection constraints:
#    BaseName (aka type) of component
#    UniqueName of component
#    base_names of each port
#    unique_names of port (and thus infer connections)
#
#    '''
#
#    num_of_components = len(list_of_components)
#
#    #declare list of constants, one for each 

if __name__ == '__main__':

    #create port_list
    port_list = PortList.bottom

    port = Port.port(BaseNames[0], UniqueNames[0])
    port1 = Port.port(BaseNames[1], UniqueNames[1])
    port_list = PortList.node(port, port_list)

    port_list = PortList.node(port1, port_list)

    #print
    print port_list
   
    c1 = Component.component(CBaseNames[0], CUniqueNames[0], port_list, PortList.bottom)

    print c1

    plist = PortList.bottom

    port_2 = Port.port(BaseNames[0], UniqueNames[1])

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
    #solver.add(define_has_port_constraints(port_list, port1))
    #solver.add(define_has_port_constraints(plist, port))

    #check condition
    #solver.add(list_has_port(plist, port_2))

    #check if component has port with name
    solver.add(define_comp_has_port_name_total([c1, c2]))
    #solver.add(define_comp_has_port_name_constraints(c1, BaseNames[1]))
    #solver.add(define_list_has_port_name_constraints(port_list, BaseNames[2]))
    solver.add(comp_has_port_base_name(x, BaseNames[2]))
    #solver.add(list_has_port_with_base_name(port_list, BaseNames[2]))

    print solver.check()
    print solver.sexpr()
    print solver.model()
