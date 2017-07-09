'''
test_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''


from pyco.examples.example_eps_facs import *
from pyco.synthesis import NotSynthesizableError, OptimizationError


"""
components are defined here as functions, 
but they canalso be directly used in the main code section
"""

def abstr_gen():
    '''
    abstract generator
    '''
    comp = AbstractGenerator('AbstractGen')
    return LibraryComponent('AbstrGenC', comp)


def dumb_gen():
    '''
    dumb generator
    '''
    comp = DumbGenerator('DumbGen')
    return LibraryComponent('DumbGenC', comp)


def std_gen():
    '''
    std generator
    '''
    comp = StdGenerator('StdGen')
    return LibraryComponent('StdGenC', comp)

def slow_gen():
    '''
    slow generator
    '''
    comp = SlowGenerator('SlowGen')
    return LibraryComponent('SlowGenC', comp)


def ac_single_back():
    '''
    ac single backup
    '''
    comp = ACSingleBackup('ACSingleBack')
    return LibraryComponent('ACSingleBackC', comp)


def ac_2_back():
    '''
    ac 2way backup
    '''
    comp = AC2WayBackup('AC2Back')
    lib_c = LibraryComponent('AC2BackC', comp)

    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2])

    return lib_c


def ac_4_back():
    '''
    ac 4 way backup
    '''
    comp = AC4WayBackup('AC4Back')
    lib_c = LibraryComponent('AC4BackC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2,
                                         comp.fail3, comp.fail4])

    return lib_c


def ac_load():
    '''
    AC load
    '''
    comp = OneSideACLoad('ACload')
    return LibraryComponent('ACLoadC', comp)


def dc_tie():
    '''
    DC tie
    '''
    comp = DCTwoSideTie('DC2Tie')
    lib_c = LibraryComponent('DC2TieC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2])

    return lib_c


def dc_load():
    '''
    dc load
    '''
    comp = DCLoadContactor('DCLoad')
    lib_c = LibraryComponent('DCLoadC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2])

    return lib_c


# MAIN FUNCTION
def test_synth_6_10_dc_1spec():
    '''
    Performs simple synthesis
    '''

    #create components
    abstr_gen_c = abstr_gen()
    dumb_gen_c = dumb_gen()
    std_gen_c = std_gen()
    slow_gen_c = slow_gen()
    ac_single_back_c = ac_single_back()
    ac_2_back_c = ac_2_back()
    ac_4_back_c = ac_4_back()
    ac_load_c = ac_load()
    dc_load_c = dc_load()
    dc_tie_c = dc_tie()

    # DEFINE LIBRARY
    library = ContractLibrary('gen_lib')

    library.add(abstr_gen_c)
    library.add(dumb_gen_c)
    library.add(std_gen_c)
    library.add(slow_gen_c)
    library.add(ac_single_back_c)
    library.add(ac_2_back_c)
    library.add(ac_4_back_c)
    library.add(ac_load_c)
    library.add(dc_load_c)
    library.add(dc_tie_c)

    # add type compatibilities
    library.add_type(GeneratorT)
    library.add_type(ACGenContactorT)
    library.add_type(ACBackContactorT)

    library.add_type_compatibility(GeneratorT, ACGenContactorT)

    #verify everything is ok
    library.verify_library()


    #define spec
    spec1 = GenIsolation1D('G1')

    # Create synthesis interface by passing the library object and a list of specifications,
    # all having the same IO interface
    interface = SynthesisInterface(library, [spec1])

    #define designer hints
    # so far, you can define:
    # same_block_constraint(list) -> specify ports of the spec that needs to be controlled by the same library block
    # and
    # distinct_ports_constraints(list) -> specify a list of ports that cannot be connected together or
    # controlled by the same port from a component in the library.

    # same_block_constraint(list)
    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])

    # distinct_ports_constraints(list)
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          spec1.fail_r1, spec1.fail_r2])

    res = None
    #synthesis phase
    try:

        # call the synthesis function.
        # Synthesis parameters are:
        #
        # limit -> None or int: specifies the maximum number of components allowed in a solutions. if None,
        #                        then the maximum number of components is the same as the number of outputs of the spec.
        #                        Default: None
        # library_max_redundancy -> None or int: specifies if the components in the library need to be replicated, and how
        #                                        many times.
        #                                        Default: None
        # strict_out_lib_map -> Boolean: specifies if all the outputs in the synthesized composition have to be connected.
        #                                I.e., do not allow unconnected outputs in the solution.
        #                                Default: False
        # strict_in_spec_map -> Boolean: specifies if all the inputs of the spec need to be connected.
        #                                Default: True
        # use_types -> Boolean: specifies if synthesis should prune the search space using types.
        #                       Default: True
        # use_hints -> Boolean: specifies if synthesis should prune the search space using designer hints.
        #                       Default: True
        # minimize_components -> Boolean: specifies if the synthesis process should minimize the number of components
        #                                 of the solution.
        #                                 Default: False
        # minimize_ports -> Boolean: specifies if the synthesis process should minimize the number of ports used
        #                                 in the solution.
        #                                 Default: False
        # minimize_cost -> Boolean: Not yet supported
        # filename -> None or str: specify the name of the output files. If None, a generic name will be used.
        #                          Default: None
        # visualize -> Boolean: if True visualize the synthesized solution when found.
        #                       Default: True
        
        interface.synthesize(strict_out_lib_map=True,
                         library_max_redundancy=2,
                         minimize_components=False,
                         minimize_ports=False,
                             filename='test_design',
                             visualize=True)
    except NotSynthesizableError:
        res = False
    else:
        res = True

    return res

if __name__ == "__main__":

    res = test_synth_6_10_dc_1spec()
    if res:
        print "success"
    else:
        print "unsynthesizable"


