"""
Implements conversion from contract to graphviz format

Author: Antonio Iannopollo
"""

import graphviz
import textwrap
import cPickle
from pyco import LOG

LINE_LENGTH = 80



class Node(object):

    def __init__(self, id, label, num_in, num_out):
        self.id = id
        self.label = label
        self.num_in = num_in
        self.num_out = num_out

    def __eq__(self, other):

        return self.id == other.id



class Graph(object):
    '''
    a generic string-based graph from the composition
    '''

    def __init__(self):

        self.edges = {}

        self.root = None
        self.sink = None
        self.attributes = {}
        self.nodes = {}
        self.reverse_nodeid_map = {}

        self.node_connection_map_outputs = {}
        self.node_connection_map_inputs = {}

    def set_attribute(self, key, attribute):
        self.attributes[key] = attribute

    def get_attribute(self, key):
        return self.attributes[key]

    def set_root(self, root):
        self.root = root
        self.nodes[root.id] = root
        self.reverse_nodeid_map[root] = root.id

    def set_sink(self, sink):
        self.sink = sink
        self.nodes[sink.id] = sink
        self.reverse_nodeid_map[sink] = sink.id

    def ugid(self, nid):
        '''
        unique graph id: makes the id unique for this graph
        :param id:
        :return:
        '''
        # if not gid == nid.split('.')[0]:
        #     return str(id(self))+'.'+nid
        # else:
        #     return nid
        return str(id(self))+'.'+nid

    @staticmethod
    def deuid(nid):

        sp = nid.split('.')

        if len(sp) > 1:
            return '.'.join(sp[1:])
        else:
            return nid

    def add_node(self, node, nid=None):
        if nid is None:
            nid = node.id
        ugid = self.ugid(nid)
        self.nodes[ugid] = node
        self.reverse_nodeid_map[node] = ugid

    def get_stored_ugid(self, node):
        return self.reverse_nodeid_map[node]

    def get_node(self, nid):
        return self.nodes[self.ugid(nid)]

    def get_nodeid(self, node):
        return self.ugid(node.id)

    def add_edge(self, idfrom, portfrom, idto, portto, label=''):


        if idfrom != self.root.id:
            idfrom = self.ugid(idfrom)

        if idto != self.sink.id:
            idto = self.ugid(idto)

        if idfrom not in self.nodes or idto not in self.nodes:
            raise KeyError

        if idfrom not in self.edges:
            self.edges[idfrom] = {}

        if portfrom not in self.edges[idfrom]:
            self.edges[idfrom][portfrom] = {}

        if idto not in self.edges[idfrom][portfrom]:
            self.edges[idfrom][portfrom][idto] = {}

        self.edges[idfrom][portfrom][idto][portto] = label

        #mapping structures
        if idfrom not in self.node_connection_map_outputs:
            self.node_connection_map_outputs[idfrom] = {}

        if idto not in self.node_connection_map_inputs:
            self.node_connection_map_inputs[idto] = {}

        if idto not in self.node_connection_map_outputs[idfrom]:
            self.node_connection_map_outputs[idfrom][idto] = set()

        if idfrom not in self.node_connection_map_inputs[idto]:
            self.node_connection_map_inputs[idto][idfrom] = set()

        self.node_connection_map_outputs[idfrom][idto].add(portfrom)
        self.node_connection_map_inputs[idto][idfrom].add(portto)

        return


    @property
    def inner_nodes(self):
        return set(self.nodes.values()) - {self.root, self.sink}

    def prune_nodes(self):
        '''
        eliminate nodes without output connections
        :return:
        '''

        to_be_removed = []
        for node in self.inner_nodes:
            nid = self.get_stored_ugid(node)
            if nid not in self.edges or len(self.edges[nid])==0:
                #remove
                to_be_removed.append(nid)

        if len(to_be_removed) == 0:
            return
        else:
            for nid in to_be_removed:
                if nid in self.nodes:
                    del self.nodes[nid]

                if nid in self.edges:
                    del self.edges[nid]
                if nid in self.node_connection_map_inputs:
                    #need to remove all the inputs to the node:
                    for nid2 in self.node_connection_map_inputs[nid]:
                        for port in self.node_connection_map_outputs[nid2][nid]:
                            if nid in self.edges[nid2][port]:
                                del self.edges[nid2][port][nid]

                        del self.node_connection_map_outputs[nid2][nid]

                    del self.node_connection_map_inputs[nid]

            #repeat till there are no changes
            self.prune_nodes()







class GraphCreator(object):
    '''
    create a generic string-based graph from the composition
    '''

    def __init__(self, spec, composed_contract, contract_list, parameters_values=None, synthesis_time=None, filename=None):
        '''
        init parameters
        '''

        self.graph = Graph()

        if filename is not None:
            filename = filename+'.gv'

        self.spec = spec
        self.contract_list = contract_list
        self.parameters_values = parameters_values


        self.graph.set_attribute('filename', filename)
        self.graph.set_attribute('assumption_str', textwrap.fill(composed_contract.assume_formula.generate(), 80))
        self.graph.set_attribute('guarantee_str', textwrap.fill(composed_contract.guarantee_formula.generate(), 80))

        if synthesis_time is not None:
            self.graph.set_attribute('synthesis_time', synthesis_time)


    def __translate_and_add_contract(self, contract):
        input_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in contract.input_ports_dict])

        #process parameters
        if self.parameters_values is None:
            str_out_ports = ['<%s> %s' % (base_name, base_name) for base_name, port in contract.output_ports_dict.items()]

        else:
            str_out_ports = ['<%s> %s' % (base_name, base_name) for base_name, port in contract.output_ports_dict.items()
                             if port.unique_name not in set(self.parameters_values.keys())]
            str_out_ports += ['<%s> %s = %s' % (base_name, base_name, str(self.parameters_values[port.unique_name]))
                              for base_name, port in contract.output_ports_dict.items()
                             if port.unique_name in set(self.parameters_values.keys())]

        output_port_str = '|'.join(str_out_ports)

        node = Node(contract.unique_name,
                    '{{%s}|%s|{%s}}' % (input_port_str, contract.base_name, output_port_str),
                    len(contract.input_ports_dict), len(contract.output_ports_dict))
        self.graph.add_node(node)

        return


    def generate_graph(self):

        spec_in_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in self.spec.input_ports_dict])
        spec_out_port_str = '|'.join(['<%s> %s' % (base_name, base_name) for base_name in self.spec.output_ports_dict])

        # add spec inputs
        root = Node('%s_in' % self.spec.base_name, 'Spec \\nInputs|%s' % spec_in_port_str,
                    len(self.spec.input_ports_dict), len(self.spec.output_ports_dict))
        self.graph.set_root(root)
        # add spec outputs
        sink = Node('%s_out' % self.spec.base_name, 'Spec \\nOutputs|%s' % spec_out_port_str,
                    len(self.spec.input_ports_dict), len(self.spec.output_ports_dict))
        self.graph.set_sink(sink)

        #add nodes
        for contract in self.contract_list:
            self.__translate_and_add_contract(contract)

        # add edges
        # spec input first
        for port in self.spec.input_ports_dict.values():
            for contract in self.contract_list:
                for cport in contract.input_ports_dict.values():
                    if port.unique_name == cport.unique_name:
                        #we have a match
                        self.graph.add_edge('%s_in' % (self.spec.base_name), port.base_name,
                                      contract.unique_name, cport.base_name,
                                        label=port.unique_name)

        #all other contracts
        for contract1 in self.contract_list:
            for port1 in contract1.output_ports_dict.values():
                for contract2 in self.contract_list:
                    for port2 in contract2.input_ports_dict.values():
                        if contract1 != contract2 and port1.unique_name == port2.unique_name:
                            self.graph.add_edge(contract1.unique_name, port1.base_name,
                                                contract2.unique_name, port2.base_name,
                                            label=port1.unique_name)

                for port in self.spec.output_ports_dict.values():
                    if port1.unique_name == port.unique_name:
                            self.graph.add_edge(contract1.unique_name, port1.base_name,
                                      '%s_out' % (self.spec.base_name), port.base_name,
                                            label=port1.unique_name)


        self.graph.prune_nodes()

        return self.graph


    def generate_pickled(self):
        '''
        serializes graph, and generates it if it has not been generated yet
        '''

        if self.graph.root is None:
            self.generate_graph()

        return cPickle.dumps(self.graph, cPickle.HIGHEST_PROTOCOL)

    @staticmethod
    def load_pickle(pickled_graph):
        return cPickle.loads(pickled_graph)


    @staticmethod
    def merge_graphs(graphs, filename):
        '''
        merge graphs which might have some parts in common.

        the assumption is that all graphs have the same root and sink
        :param graphs:
        :return:
        '''

        new_graph = Graph()
        new_graph.set_attribute('filename', filename+'.gv')

        new_graph.set_root(graphs[0].root)
        new_graph.set_sink(graphs[0].sink)

        for g in graphs:
            for n in g.inner_nodes:
                new_graph.add_node(n, nid=g.get_stored_ugid(n))

            for idfrom in g.edges:
                for portfrom in g.edges[idfrom]:
                    for idto in g.edges[idfrom][portfrom]:
                        for portto in g.edges[idfrom][portfrom][idto]:
                            label = g.edges[idfrom][portfrom][idto][portto]

                            new_graph.add_edge(idfrom, portfrom, idto, portto, label=label)



        #now we need to merge replicated nodes:
        front = set()
        processing = {new_graph.root.id}
        done = set()

        while len(processing) > 0:

            #add all nodes which were connected to processing
            for n in processing:
                if n in new_graph.node_connection_map_outputs:
                    front = front | set(new_graph.node_connection_map_outputs[n].keys())

            #move processing to done
            done = done | processing
            processing = set()

            #find all the nodes in front who are ready to be processed
            for n in front:
                #get all the connected components to the node
                cnodes = set(new_graph.node_connection_map_inputs[n].keys())

                if all([c in done for c in cnodes]):
                    #good, we have all the connection for this node
                    processing.add(n)


            #update front
            front = front - processing

            #now check in processing if there are redundant nodes
            #first, find identical nodes:
            seen = set()
            for n in processing:
                if n not in seen:
                    seen.add(n)

                    same = {x for x in processing - {n} if new_graph.nodes[x].label == new_graph.nodes[n].label}

                    #now we need to check that all the inputs are the same.

                    for c in same:
                        fail = False
                        if not ({Graph.deuid(x) for x in new_graph.node_connection_map_inputs[n].keys()} ==
                            {Graph.deuid(x) for x in new_graph.node_connection_map_inputs[c].keys()}):
                            #they don't get inputs from the same nodes
                            fail = True
                            continue

                        connected_nodes = set()
                        for nodefrom in new_graph.node_connection_map_inputs[n]:
                            if fail:
                                break

                            match = [x for x in set(new_graph.node_connection_map_inputs[c])-connected_nodes
                                    if new_graph.nodes[x].label == new_graph.nodes[nodefrom].label]

                            if len(match) == 0:
                                fail = True
                                break
                            else:
                                # connected_nodes.add(match[0])

                            # for nodefrom2 in new_graph.node_connection_map_inputs[c]:
                            #
                            #     if new_graph.nodes[nodefrom].label != new_graph.nodes[nodefrom2].label:
                            #         #if the node label isn't the same
                            #         #TODO check if this is redundant with the check above
                            #         fail = True
                            #         break
                                found = False
                                for nodefrom2 in match:
                                    if found:
                                        break
                                    #same node. now check all connections match
                                    # for portfrom in new_graph.edges[nodefrom]:
                                    for portfrom in new_graph.node_connection_map_outputs[nodefrom][n]:
                                        if found:
                                            break

                                        if portfrom in new_graph.edges[nodefrom2]:

                                            #same port from
                                            #TODO this is maybe useless?
                                            if (n in new_graph.edges[nodefrom][portfrom] and c in new_graph.edges[nodefrom2][portfrom]):
                                                # same input port

                                                for portto in new_graph.edges[nodefrom][portfrom][n]:
                                                    if portto in new_graph.edges[nodefrom2][portfrom][c]:
                                                        found = True
                                                        connected_nodes.add(nodefrom2)
                                                        break
                                if not found:
                                    fail = True
                                    break

                        if not fail:
                            #if we made so far, we have a match

                            # we need to make sure all the connections are updated
                            seen.add(c)
                            if c in new_graph.edges:
                                for portfrom in new_graph.edges[c]:
                                    for idto in new_graph.edges[c][portfrom]:
                                        for portto in new_graph.edges[c][portfrom][idto]:
                                            label = new_graph.edges[c][portfrom][idto][portto]

                                            new_graph.add_edge(new_graph.deuid(n), portfrom, new_graph.deuid(idto), portto, label=label)

                                #remove all outputs, prune_nodes() will take care of the rest
                                # for p in new_graph.edges[c]:
                                #     new_graph.edges[c][p] = {}
                                del new_graph.edges[c]
                                del new_graph.node_connection_map_outputs[c]
                                for nid in new_graph.node_connection_map_inputs:
                                    if c in new_graph.node_connection_map_inputs[nid]:
                                        del new_graph.node_connection_map_inputs[nid][c]


            #done

        #cleanup
        new_graph.prune_nodes()
        return new_graph




class GraphizConverter(object):
    def __init__(self, spec, composed_contract, contract_list, parameters_values=None, synthesis_time=None, filename=None):

        if filename is not None:
            filename = filename+'.gv'

        self.spec = spec
        self.contract_list = contract_list
        self.parameters_values = parameters_values

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

        #process parameters
        if self.parameters_values is None:
            str_out_ports = ['<%s> %s' % (base_name, base_name) for base_name, port in contract.output_ports_dict.items()]

        else:
            str_out_ports = ['<%s> %s' % (base_name, base_name) for base_name, port in contract.output_ports_dict.items()
                             if port.unique_name not in set(self.parameters_values.keys())]
            str_out_ports += ['<%s> %s = %s' % (base_name, base_name, str(self.parameters_values[port.unique_name]))
                              for base_name, port in contract.output_ports_dict.items()
                             if port.unique_name in set(self.parameters_values.keys())]

        output_port_str = '|'.join(str_out_ports)

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


    @staticmethod
    def generate_graphviz_from_generic_graph(graph):
        '''
        generate graphviz from generic graph
        :param graph:
        :return:
        '''

        gv = graphviz.Digraph('pyco_out', filename=graph.attributes['filename'],
                                      node_attr={'shape': 'Mrecord'},)

        label_str = ''
        if 'synthesis_time' in graph.attributes:
            label_str = 'Synthesis time: %.2f seconds\n\n %s' % (graph.attributes['synthesis_time'], label_str)

        gv.attr(label=label_str,
                   labelloc='b', labeljust='center',
                   rankdir='LR',
                   splines='polyline',
                   compound='true'
                   )

        # add spec inputs
        gv.node(graph.get_stored_ugid(graph.root), graph.root.label, shape='record',
                        rank='source')

        for node in graph.inner_nodes:
            gv.node(graph.get_stored_ugid(node),
                       label=node.label)

        # add spec outputs
        gv.node(graph.get_stored_ugid(graph.sink), graph.sink.label, shape='record',
                        rank='sink')

        #add edges
        for source in graph.edges:
            if len(graph.edges[source]) > 0:
                for portfrom in graph.edges[source]:
                    for dest in graph.edges[source][portfrom]:
                        for portto in graph.edges[source][portfrom][dest]:
                            label = graph.edges[source][portfrom][dest][portto]
                            gv.edge('%s:%s' % (source, portfrom),
                                    '%s:%s' % (dest, portto),
                                    label=label)


        return gv

    def view(self):
        self.graph.view()
        # LOG.debug(self.graph.source)

    def save(self):
        # self.graph.save()
        self.graph.render()
        # LOG.debug(self.graph.source)

