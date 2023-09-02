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
import time

MAX_THREADS = 10

#NotSynthesizableError = z3_interface.NotSynthesizableError

class ModelVerificationManager(object):
    '''
    manages refinement threads
    '''

    def __init__(self, solver_interface, output_port_names, semaphore):
        '''
        set up solver and thread status
        '''

        self.solver = solver_interface.solver
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
        self.z3_lock = multiprocessing.Lock()
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
            try:
                # with self.z3_lock:
                model = self.solver_interface.propose_candidate()
                LOG.debug(model)
                    # LOG.debug(time.time()-tim)
                    # tim = time.time()
            except pyco.z3_interface.NotSynthesizableError as err:
                return self.quit(wait=True)
            else:
                #acquire semaphore
                self.semaphore.acquire()

                #check if event is successful
                if self.found_refinement.is_set():
                    #we are done. kill all running threads and exit
                    self.semaphore.release()
                    return self.quit()

                #else remove not successful models
                while not self.fail_queue.empty():
                    pid = self.fail_queue.get_nowait()
                    self.model_dict.pop(pid)

                    self.thread_pool = self.thread_pool - set([t for t in self.thread_pool if t.ident == pid])

                # NUXMV MOD
                #return all contracts here
                relevant = {x
                 for x, m in self.solver_interface.lib_model.use_flags.items()}

                print(len(relevant))
                print(len(self.solver_interface.z3_interface.library.all_contracts))

                reject_f = self.solver_interface.generate_reject_formula(relevant)
                #new refinement checker
                thread = RefinementChecker(model, self.output_port_names, relevant, self, self.found_refinement, self.found_refinement)
                #go
                thread.start()
                # with self.pool_lock:
                self.model_dict[thread.ident] = model
                self.relevant_contracts_pid[thread.ident] = relevant
                self.thread_pool.add(thread)

                #now reject the model, to get a new candidate
                LOG.debug(reject_f)
                self.solver_interface.add_assertions(reject_f)

                #NUXMV MOD
                #quit
                return self.quit(wait=True)

    def quit(self, wait=False):
        '''
        close up nicely
        '''

        print('')
        if not wait:
            LOG.debug('terminating')
            self.terminate_event.set()

        # LOG.debug(self.thread_pool)
        for thread in self.thread_pool:
            thread.join()

        if self.found_refinement.is_set():
            LOG.debug("get solution")
            pids = []
            var_assign_pid = {}
            params_pid = {}
            while not self.result_queue.empty():
                pid, model_map_items, params_items = self.result_queue.get()
                pids.append(pid)
                var_assign_pid[pid] = {k: v for (k, v) in model_map_items}
                params_pid[pid] = {k: v for (k, v) in params_items}

            pid = min(pids)
        else:
            raise pyco.z3_interface.NotSynthesizableError()

        self.model = self.model_dict[pid]
        self.var_assign = var_assign_pid[pid]
        self.params_assign = params_pid[pid]
        self.relevant_contracts = self.relevant_contracts_pid[pid]

        #rebuild composition
        self.composition, self.connected_spec, self.contract_inst = \
                self.solver_interface.build_composition_from_model(self.model, self.output_port_names,
                                                                   self.relevant_contracts, self.var_assign)

        return (self.model, self.composition, self.connected_spec, self.contract_inst, self.params_assign)


class RefinementChecker(multiprocessing.Process):
    '''
    this thread executes a refinement checks and dies
    '''

    def __init__(self, model, output_port_names, relevant_contracts, manager, found_event, terminate_event):
        '''
        instantiate
        '''
        self.model = model
        self.solver_interface = manager.solver_interface
        self.found_event = found_event
        self.manager = manager
        self.z3_lock = manager.z3_lock
        self.terminate_event = terminate_event

        self.output_port_names = output_port_names
        self.relevant_contracts = relevant_contracts

        super(RefinementChecker, self).__init__()

    def run(self):
        '''
        executes refinement check
        '''
        state = \
            counterexample_analysis(self.solver_interface.specification_list, self.output_port_names,
                                    self.model, self.relevant_contracts, self.solver_interface, self.pid, self.found_event,
                                    self.manager.result_queue, self.terminate_event)

        if not state:
            self.manager.fail_queue.put(self.pid)

        #we are done, release semaphore
        self.manager.semaphore.release()

        #LOG.debug('done')

        return
