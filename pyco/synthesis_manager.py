'''
This module manages the refinement checks using a set
of threads to speed things up

Author: Antonio Iannopollo
'''

import multiprocessing

# import threading
# from Queue import Queue, Empty
import pyco
from pyco import LOG
from counterxample_analysis import counterexample_analysis

# MAX_THREADS = 10

class ModelVerificationManager(object):
    '''
    manages refinement threads
    '''

    def __init__(self, solver_interface, output_port_names, semaphore):
        '''
        set up solver and thread status
        '''

        # self.solver = solver_interface.solver
        self.solver_interface = solver_interface
        self.spec = self.solver_interface.spec
        self.spec_out_dict = self.spec.output_ports_dict
        self.semaphore = semaphore
        self.found_refinement = multiprocessing.Event()

        self.composition = None
        self.connected_spec = None
        self.contract_inst = None
        self.model = None
        self.model_map = None

        self.solution_lock = multiprocessing.Lock()
        self.constraint_queue = multiprocessing.Queue()

        self.thread_pool = set()
        self.pool_lock = multiprocessing.RLock()
        self.terminate_event = multiprocessing.Event()
        self.result_queue = multiprocessing.Queue()
        self.fail_queue = multiprocessing.Queue()

        self.model_dict = {}
        self.output_port_names = output_port_names
        self.relevant_contracts_pid = {}

    def set_successful_candidate(self, model, composition, connected_spec, contract_inst):
        '''
        allows execution threads to set a result when found
        '''
        #non-blocking
        if self.solution_lock.acquire(False):
            if self.model is None:
                self.composition = composition
                self.connected_spec = connected_spec
                self.contract_inst = contract_inst
                self.model = model

            self.solution_lock.release()

        return

    def synthesize(self):
        '''
        picks candidates and generates threads
        '''
        while True:
            #acquire semaphore
            # self.semaphore.acquire()

            #check if event is successful
            if self.found_refinement.is_set():
                #we are done. kill all running threads and exit
                self.semaphore.release()
                return self.quit()

            #else remove not successful models
            # while not self.fail_queue.empty():
            #     pid = self.fail_queue.get_nowait()
            #     self.model_dict.pop(pid)

            #     self.thread_pool = self.thread_pool - set([t for t in self.thread_pool if t.ident == pid])

            # NUXMV MOD
            #return all contracts here
            # relevant = {x
                # for x, m in self.solver_interface.lib_model.use_flags.items()}
            relevant = set(self.solver_interface.library.all_contracts)

            # print(len(relevant))
            # print(len(self.solver_interface.library.all_contracts))

            # reject_f = self.solver_interface.generate_reject_formula(relevant)
            #new refinement checker
            checker = RefinementChecker(self.output_port_names, relevant, self, self.found_refinement, self.found_refinement)
            #go
            var_assign, param_assign = checker.run()
            # self.relevant_contracts_pid[checker.ident] = relevant
            # self.thread_pool.add(checker)

            #now reject the model, to get a new candidate
            # LOG.debug(reject_f)
            # self.solver_interface.add_assertions(reject_f)

            #NUXMV MOD
            #quit
            # return self.quit(wait=True)
            if var_assign is None:
                raise pyco.cegis_interface.NotSynthesizableError()

            self.var_assign = var_assign
            self.params_assign = param_assign
            # self.relevant_contracts = self.relevant_contracts_pid[pid]

            #rebuild composition
            self.composition, self.connected_spec, self.contract_inst = \
                    self.solver_interface.build_composition_from_model(self.output_port_names,
                                                                    relevant, self.var_assign)

            return (self.composition, self.connected_spec, self.contract_inst, self.params_assign)

    def quit(self, wait=False):
        '''
        close up nicely
        '''

        print('')
        if not wait:
            LOG.debug('terminating')
            self.terminate_event.set()

        # LOG.debug(self.thread_pool)
        # for thread in self.thread_pool:
        #     thread.join()

        if self.found_refinement.is_set():
            LOG.debug("get solution")
            # TODO: pids are now just references to the objects (to be verified)
            # in fact, we might not need this at all.
            pids = []
            var_assign_pid = {}
            params_pid = {}
            while not self.result_queue.empty():
                pid, model_map_items, params_items = self.result_queue.get()
                pids.append(pid)
                var_assign_pid[pid] = {k: v for (k, v) in model_map_items}
                params_pid[pid] = {k: v for (k, v) in params_items}

            # pid = min(pids)
            LOG.debug('results found: %d' % len(pids))
            pid = pids[0]
        else:
            raise pyco.cegis_interface.NotSynthesizableError()

        self.model = self.model_dict[pid]
        self.var_assign = var_assign_pid[pid]
        self.params_assign = params_pid[pid]
        self.relevant_contracts = self.relevant_contracts_pid[pid]

        #rebuild composition
        self.composition, self.connected_spec, self.contract_inst = \
                self.solver_interface.build_composition_from_model(self.model, self.output_port_names,
                                                                   self.relevant_contracts, self.var_assign)

        return (self.model, self.composition, self.connected_spec, self.contract_inst, self.params_assign)


class RefinementChecker(object):
    '''
    this thread executes a refinement checks and dies
    '''

    def __init__(self, output_port_names, relevant_contracts, manager, found_event, terminate_event):
        '''
        instantiate
        '''
        self.solver_interface = manager.solver_interface
        self.found_event = found_event
        self.manager = manager
        # self.z3_lock = manager.z3_lock
        self.terminate_event = terminate_event

        self.output_port_names = output_port_names
        self.relevant_contracts = relevant_contracts

        super(RefinementChecker, self).__init__()

    def run(self):
        '''
        executes refinement check
        '''
        var_assign, param_assign = \
            counterexample_analysis(self.solver_interface.specification_list, self.output_port_names,
                                    self.relevant_contracts, self.solver_interface, self, self.found_event,
                                    self.manager.result_queue, self.terminate_event)

        # if not state:
        #     self.manager.fail_queue.put(self)

        #we are done, release semaphore
        # self.manager.semaphore.release()

        #LOG.debug('done')

        return var_assign, param_assign
