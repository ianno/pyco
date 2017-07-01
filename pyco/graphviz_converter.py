"""
Implements conversion from contract to graphviz format

Author: Antonio Iannopollo
"""

import graphviz
import textwrap
from pyco import LOG

LINE_LENGTH = 80


class GraphizConverter(object):
    def __init__(self, spec, composed_contract, contract_list, synthesis_time=None, filename=None):

        if filename is not None:
            filename = filename+'.gv'

        self.spec = spec
        self.contract_list = contract_list

        self.graph = graphviz.Digraph('pyco_out', filename=filename,
                                      node_attr={'shape': 'Mrecord'},)

        assumption_str = textwrap.fill(composed_contract.assume_formula.generate(), 80)
        guarantee_str = textwrap.fill(composed_contract.guarantee_formula.generate(), 80)

        label_str = 'Composition Assumptions: %s \n\n' \
                    'Composition Guarantees: %s' % (assumption_str, guarantee_str)

        if synthesis_time is not None:
            label_str = 'Synthesis time: %.2f seconds\n\n %s' % (synthesis_time, label_str)

        self.graph.attr(label=label_str,
                        labelloc='b', labeljust='center',
                        rankdir='LR',
                        splines='polyline',
                        compound='true'
                        )

    def __translate_and_add_contract(self, contract, graph):
        input_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in contract.input_ports_dict])
        output_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in contract.output_ports_dict])

        graph.node(contract.unique_name,
                        label='{{%s}|%s|{%s}}' % (input_port_str, contract.base_name, output_port_str))

        return


    def generate_graphviz(self):

        #spec is special, we have ports at the beginning and the end of the graph

        spec_in_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in self.spec.input_ports_dict])
        spec_out_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in self.spec.output_ports_dict])

        #add spec inputs
        self.graph.node('%s_in' % self.spec.base_name, 'Spec \\nInputs|%s' % spec_in_port_str, shape='record', rank='source')

        for contract in self.contract_list:
            self.__translate_and_add_contract(contract, self.graph)

        #add spec outputs
        self.graph.node('%s_out' % self.spec.base_name, 'Spec \\nOutputs|%s' % spec_out_port_str, shape='record', rank='sink')

        #add edges
        #spec input first
        for port in self.spec.input_ports_dict.values():
            for contract in self.contract_list:
                for cport in contract.input_ports_dict.values():
                    if port.unique_name == cport.unique_name:
                        #we have a match
                        self.graph.edge('%s_in:%s' % (self.spec.base_name, port.base_name),
                                      '%s:%s' % (contract.unique_name, cport.base_name),
                                        label=port.unique_name)

        #all other contracts
        for contract1 in self.contract_list:
            for port1 in contract1.output_ports_dict.values():
                for contract2 in self.contract_list:
                    for port2 in contract2.input_ports_dict.values():
                        if contract1 != contract2 and port1.unique_name == port2.unique_name:
                            self.graph.edge('%s:%s' % (contract1.unique_name, port1.base_name),
                                          '%s:%s' % (contract2.unique_name, port2.base_name),
                                            label=port1.unique_name)

                for port in self.spec.output_ports_dict.values():
                    if port1.unique_name == port.unique_name:
                            self.graph.edge('%s:%s' % (contract1.unique_name, port1.base_name),
                                      '%s_out:%s' % (self.spec.base_name, port.base_name),
                                            label=port1.unique_name)

        return

    def view(self):
        self.graph.view()
        LOG.debug(self.graph.source)

    def save(self):
        # self.graph.save()
        self.graph.render()
        LOG.debug(self.graph.source)

