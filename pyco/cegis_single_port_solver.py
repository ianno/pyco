'''
This module includes classess and methods to synthesize a solution for a single port of the specification.
Each solver has its own process

Author: Antonio Iannopollo
'''

import pyco
from pyco import LOG
import itertools
from time import time

import types
from z3 import *
import multiprocessing

from pycolite.contract import CompositionMapping
from pyco.synthesis_manager import ModelVerificationManager
# from pyco.z3_library_conversion import Z3Library
# from threading import Thread
# from multiprocessing import Pool, Process, Queue
# from Queue import Queue
from graphviz_converter import Graph, GraphCreator

import time

# MAX_SOLVERS = 10

class SinglePortSolver(multiprocessing.Process):
    '''
    this process synthesizes a solution for a single output port
    '''

    def __init__(self, synthesis_interface,
                 spec_port_names, semaphore, spec,
                 minimize_components=False,
                 distinct_spec_port_set=None,
                 fixed_components=None,
                 fixed_connections=None,
                 fixed_connections_spec=None,
                 result_queue=None,
                 visualize=True
                 ):

        # set_option(verbose=15)
        # set_option(proof=False)

        self.synthesis_interface = synthesis_interface
        self.max_depth = synthesis_interface.max_depth

        # self.type_compatibility_set = z3_interface.type_compatibility_set
        # self.type_incompatibility_set = z3_interface.type_incompatibility_set

        self.semaphore = semaphore

        self.spec = spec
        # self.context = context
        # self.assertions = assertions
        self.spec_port_names = spec_port_names
        self.spec_out_dict = self.spec.output_ports_dict

        self.num_out = len(self.spec_out_dict)

        # self.lib_model = self.synthesis_interface.lib_model
        self.library = self.synthesis_interface.library

        # self.lib_model.instantiate_models(context=self.context)


        self.specification_list = self.synthesis_interface.specification_list

        # optimize = minimize_components

        self.distinct_spec_port_set = {}
        if distinct_spec_port_set is not None:
            self.distinct_spec_port_set = distinct_spec_port_set

        self.fixed_components = {}
        if fixed_components is not None:
            self.fixed_components = fixed_components

        self.fixed_connections = {}
        if fixed_connections is not None:
            self.fixed_connections = fixed_connections
        self.fixed_connections_spec = {}
        if fixed_connections_spec is not None:
            self.fixed_connections_spec = fixed_connections_spec

        self.result_queue = result_queue
        self.visualize = visualize

        super(SinglePortSolver, self).__init__()

    def run(self):

        model_manager = ModelVerificationManager(self, self.spec_port_names, self.semaphore)

        try:
            (composition,
                spec, contract_list, params_assign) = model_manager.synthesize()
        except NotSynthesizableError:
            print("No solution for spec over variables " + str(self.spec_port_names))
            print(spec)
            self.result_queue.put(None)
            raise
        else:
            # LOG.info(model)
            for c in contract_list:
                LOG.info(c)

            print("For spec over variables " + str(self.spec_port_names))
            print(spec)
            print("Found solution ")
            print(composition)

            graph = Graph()
            if self.visualize:
                graph = GraphCreator(spec, composition, contract_list, parameters_values=params_assign, filename='_'.join(self.spec_port_names))
                graph = graph.generate_graph()

                LOG.debug('push results')
            self.result_queue.put(graph)

            return

    def retrieve_fixed_components(self):
        '''
        return fixed components
        :return:
        '''
        return self.synthesis_interface.retrieve_fixed_components()

    def __find_configurations_for_contract(self, seen, used, contract,
                                           all_contracts, connection_map, upper_list):
        '''
        fill possible configurations dict up to a certain depth
        :param depth:
        :param contract:
        :param all_contracts:
        :param connection_map:
        :return:
        '''

        for conf in connection_map[contract]:
            if conf <= (all_contracts - used):

                conf_dict = {}

                for c in conf - seen:
                    seen.add(c)
                    c_list = []
                    self.__find_configurations_for_contract(seen, used | {c}, c,
                                                            all_contracts,
                                                            connection_map,
                                                            c_list)

                    conf_dict[c] = c_list

                if len(conf_dict) > 0:
                    upper_list.append(conf_dict)

        return

    def build_composition_from_model(self, output_port_names, relevant_contracts, var_assign, params=None, build_copy=False):
        '''
        builds a contract composition out of a model
        :param output_port_name:
        '''


        spec = self.spec.copy()
        working_spec = spec.copy()

        processed_ports = set()
        used_contracts = set()

        #used for copies, maps to itself if not a copy
        relevant_map = {c: c for c in relevant_contracts}

        if build_copy:
            relevant_copies = {x:x.copy() for x in relevant_contracts}
            relevant_map = {p:c for c,p in relevant_copies.items()}

            relevant_contracts = { c for c in relevant_copies.values()}

            uname_map = {p.unique_name: relevant_copies[c].ports_dict[p.base_name].unique_name
                         for c in relevant_copies for p in c.ports_dict.values()}

            var_c = var_assign
            var_assign = copy.deepcopy(var_c)

            for un in var_c:
                name = un
                if un in uname_map:
                    name = uname_map[un]
                    var_assign[name] = var_c[un]
                    del var_assign[un]


                uun = var_c[un]
                if uun in uname_map:
                    var_assign[name] = uname_map[uun]

            if params is not None:
                params = {uname_map[uname]: params[uname] for uname in params}




        mapping = CompositionMapping(relevant_contracts| {working_spec})

        temp_spec_used = False

        # start with spec
        for bname in output_port_names:
            port = spec.ports_dict[bname]
            for c in relevant_contracts:
                done = False

                for obname, oport in c.output_ports_dict.items():
                    ouname = oport.unique_name

                    if bname in var_assign:
                        if ouname == var_assign[bname]:
                            spec.connect_to_port(port, oport)
                            done = True
                            used_contracts.add(c)
                            break
                    else:
                        #pick any other port
                        LOG.debug(self.library.spec_out_map)
                        if c in self.library.spec_out_map[bname]:
                            if self.library.check_connectivity(port, oport):
                                spec.connect_to_port(port, oport)
                                done = True
                                used_contracts.add(c)
                                break

                if done:
                    break

        stack = {x for x in used_contracts}

        # connections among candidates
        while len(stack) > 0:
            c1 = stack.pop()
            used_contracts.add(c1)

            for n1, p1 in c1.input_ports_dict.items():
                u1 = p1.unique_name
                done = False
                for c2 in relevant_contracts:

                    done = False
                    if u1 in var_assign:
                        for n2, p2 in c2.output_ports_dict.items():
                            u2 = p2.unique_name

                            if u2 == var_assign[u1]:
                                mapping.connect(p1, p2,
                                                '%s_%s' % (c1.unique_name,
                                                           p1.base_name))
                                done = True
                                processed_ports.add(p1)
                                processed_ports.add(p2)
                                if c2 not in used_contracts:
                                    stack.add(c2)
                                break

                    else:
                        for conf in self.library.connection_map[relevant_map[c1]]:
                            if relevant_map[c2] in conf:
                                for n2, p2 in c2.output_ports_dict.items():
                                    u2 = p2.unique_name
                                    if self.library.check_connectivity(p1, p2):
                                        mapping.connect(p1, p2,
                                                        '%s_%s' % (c1.unique_name,
                                                                   n1))
                                        done = True
                                        processed_ports.add(p1)
                                        processed_ports.add(p2)
                                        if c2 not in used_contracts:
                                            stack.add(c2)
                                        break
                                if done:
                                    break
                    if done:
                        break

                #spec
                if not done:
                    for n2, p2 in spec.input_ports_dict.items():

                        if u1 in var_assign and n2 == var_assign[u1]:
                            spec.connect_to_port(p2, p1)
                            processed_ports.add(p1)
                            processed_ports.add(p2)
                            break

        if build_copy:
            relevant_contracts = used_contracts | {relevant_copies[x] for x in self.retrieve_fixed_components()}
        else:
            relevant_contracts = used_contracts | self.retrieve_fixed_components()

        for c in relevant_contracts:
            for p in c.ports_dict.values():
                if p not in processed_ports:
                    mapping.add(p, '%s_%s' % (c.unique_name,
                                                         p.base_name))
                    processed_ports.add(p)

        if temp_spec_used:
            composition = working_spec.compose(relevant_contracts, composition_mapping=mapping)
        else:
            root = relevant_contracts.pop()
            composition = root.compose(relevant_contracts, composition_mapping=mapping)
            relevant_contracts.add(root)

        LOG.debug(composition)
        for c in relevant_contracts:
            LOG.debug(c)

        if params is None:
            return composition, spec, relevant_contracts
        else:
            return composition, spec, relevant_contracts, params

class NotSynthesizableError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass

class OptimizationError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass