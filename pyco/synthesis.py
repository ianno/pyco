'''
Synthesizer interface

Author: Antonio Iannopollo
'''

import itertools

from pyco.contract import EmptyContract
from pyco.z3_interface import Z3Interface, NotSynthesizableError, OptimizationError
from pyco.graphviz_converter import GraphizConverter
import time
from pyco import LOG


class SynthesisInterface(object):
    '''
    Interface for synthesis
    '''

    def __init__(self, library, spec_contract_list=[EmptyContract('Void')], limit=None):
        '''
        constructor
        '''

        self.spec_contract_list = spec_contract_list
        self.library = library

        self.same_block_pairs = set()
        self.distinct_map = set()

        self.fixed_components = set()
        self.fixed_connections = set()
        self.fixed_connections_spec = set()

        self.solver_interface = Z3Interface(library)


    def same_block_constraint(self, port_list):
        '''
        Assert a set of ports to be implemented by the same block
        '''

        for (port_1, port_2) in itertools.combinations(port_list, 2):
           self.same_block_pairs.add((port_1.base_name, port_2.base_name))

    def distinct_ports_constraints(self, port_list):
        '''
        specifies a set of ports that cannot have same mapped
        ports
        '''
        for (port_1, port_2) in itertools.combinations(port_list, 2):
           self.distinct_map.add((port_1.base_name, port_2.base_name))

    def get_lib_redundancy_level(self):
        """
        :return: the redundancy level of the library
        """
        return self.solver_interface.lib_model.max_components

    def get_component(self, name, level=0):
        """
        Returns the specified component
        :param name: name of the component
        :param level: level of the chosen component, in case elements in the library are redundant
        :return: the specified component at the requested level
        """
        return self.solver_interface.library.component_by_name(name)


    def use_component(self, component, level=0):
        """
        Use component in synthesis
        :param component:
        :param level:
        :return:
        """

        self.fixed_components.add((component, level))


    def use_connected(self, comp1, port1_name, comp2, port2_name, level1=0, level2=0):
        """
        Use component in synthesis
        :param component:
        :param level:
        :return:
        """

        self.fixed_components.add((comp1, level1))
        self.fixed_components.add((comp2, level2))
        self.fixed_connections.add((comp1, port1_name, level1, comp2, port2_name, level2))

    def use_connected_spec(self, comp, port_name, spec_port_name, level=0):
        """
        Use component in synthesis
        :param component:
        :param level:
        :return:
        """

        self.fixed_components.add((comp, level))
        self.fixed_connections_spec.add((comp, port_name, level, spec_port_name))

    def synthesize(self, limit=None, library_max_redundancy=None,
                   strict_out_lib_map=False,
                   strict_in_spec_map=True,
                   use_types=True,
                   use_hints=True,
                   minimize_components=False,
                   minimize_ports=False,
                   minimize_cost=False,
                   filename=None,
                   visualize=True
                   ):
        '''
        call for synthesis
        '''
        LOG.debug(filename)
        if filename is None:
            filename = 'out'

        time1 = time.time()

        (model, composition,
         spec, contract_list) = self.solver_interface.synthesize(self.spec_contract_list, limit=limit,
                                         library_max_redundancy=library_max_redundancy,
                                         strict_out_lib_map=strict_out_lib_map,
                                         strict_in_spec_map=strict_in_spec_map,
                                         use_types=use_types,
                                         use_hints=use_hints,
                                         minimize_components=minimize_components,
                                         minimize_ports=minimize_ports,
                                         minimize_cost=minimize_cost,
                                         same_block_constraints=self.same_block_pairs,
                                         distinct_mapping_constraints=self.distinct_map,
                                         fixed_components=self.fixed_components,
                                         fixed_connections=self.fixed_connections,
                                         fixed_connections_spec=self.fixed_connections_spec)
        time2 = time.time()
        graphviz_conv = GraphizConverter(spec, composition, contract_list,
                                         synthesis_time=time2-time1, filename=filename)
        graphviz_conv.generate_graphviz()

        if visualize:
            graphviz_conv.view()
        else:
            graphviz_conv.save()

        with open(filename+'.pyco', 'w') as f:
            f.write('Synthesis time: %.2f seconds\n\n\n' % (time2-time1))
            f.write(str(model))
            f.write('\n\n')
            f.write(str(spec))
            f.write('\n\n')
            for c in contract_list:
                f.write(str(c))
                f.write('\n')
