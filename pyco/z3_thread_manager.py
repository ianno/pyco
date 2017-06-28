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

MAX_THREADS = 7

#NotSynthesizableError = z3_interface.NotSynthesizableError

class ModelVerificationManager(object):
    '''
    manages refinement threads
    '''

    def __init__(self, z3_interface):
        '''
        set up solver and thread status
        '''

        self.solver = z3_interface.solver
        self.z3_interface = z3_interface
        self.semaphore = multiprocessing.Semaphore(MAX_THREADS)
        self.found_refinement = multiprocessing.Event()

        self.composition = None
        self.connected_spec = None
        self.contract_inst = None
        self.model = None

        self.solution_lock = multiprocessing.Lock()
        self.z3_lock = multiprocessing.Lock()
        self.constraint_queue = multiprocessing.Queue()

        self.thread_pool = set()
        self.pool_lock = multiprocessing.RLock()
        self.terminate_event = multiprocessing.Event()
        self.result_queue = multiprocessing.Queue()
        self.fail_queue = multiprocessing.Queue()

        self.model_dict = {}

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
                #self.solution_models = solution_models
                self.model = model

            self.solution_lock.release()

        return

    def synthesize(self, size_constraints, initial_size):
        '''
        picks candidates and generates threads
        '''
        #testing without size constraints
        #size = 1
        size = initial_size

        while True:
            try:
                with self.z3_lock:
                    model = self.z3_interface.propose_candidate()
            except pyco.z3_interface.NotSynthesizableError as err:
                if size < self.z3_interface.max_components:
                    # # this should happen anymore
                    # LOG.debug('Synthesis for size %d failed. Increasing number of components...', size)
                    # size = size + 1
                    # with self.z3_lock:
                    #     self.solver.pop()
                    #     self.solver.push()
                    #     self.solver.add(size_constraints[size])
                    pass
                else:
                    return self.terminate()
            else:
                #acquire semaphore
                self.semaphore.acquire()

                #check if event is successful
                if self.found_refinement.is_set():
                    #we are done. kill all running threads and exit

                    return self.terminate()

                #else remove not successful models
                while not self.fail_queue.empty():
                    pid = self.fail_queue.get_nowait()
                    self.model_dict.pop(pid)

                #new refinement checker
                thread = RefinementChecker(model, self, self.found_refinement)
                #go
                thread.start()
                with self.pool_lock:
                    self.model_dict[thread.pid] = model
                    self.thread_pool.add(thread)

                #now reject the model, to get a new candidate
                #LOG.debug('pre-lock')
                with self.z3_lock:
                    #LOG.debug('pre-reject')
                    self.solver.add(self.z3_interface.reject_candidate(model))
                    #LOG.debug('done')


    def terminate(self):
        '''
        close up nicely
        '''
        print('')
        LOG.debug('terminating')
        #pid = self.result_queue.get()

        with self.pool_lock:
            self.terminate_event.set()

        for thread in self.thread_pool:
            thread.join()

        if self.found_refinement.is_set():
            pids = []
            while not self.result_queue.empty():
                pids.append(self.result_queue.get())
            pid = min(pids)
        else:
            raise pyco.z3_interface.NotSynthesizableError()

        self.model = self.model_dict[pid]

        #rebuild composition
        spec = self.z3_interface.specification_list[0]
        with self.z3_lock:
            self.composition, self.connected_spec, self.contract_inst = \
                    self.z3_interface.build_composition_from_model(self.model, spec, complete_model=True)
        #wait for all the threads to stop


        #for thread in self.thread_pool:
        #    thread.join()

        return (self.model, self.composition, self.connected_spec, self.contract_inst)


class RefinementChecker(multiprocessing.Process):
    '''
    this thread executes a refinement checks and dies
    '''

    def __init__(self, model, manager, found_event):
        '''
        instantiate
        '''
        self.model = model
        self.z3_interface = manager.z3_interface
        self.found_event = found_event
        self.manager = manager
        self.z3_lock = manager.z3_lock
        #self.result_queue = multiprocessing.Queue()

        super(RefinementChecker, self).__init__()


    def check_all_specs_threadsafe(self, model, z3_lock):
        '''
        check if the model satisfies a number of specs, if provided
        '''

        composition = None
        connected_spec = None
        contract_inst = None
        failed_spec = None
        for spec in self.z3_interface.specification_list:
            with z3_lock:
                composition, connected_spec, contract_inst = \
                    self.z3_interface.build_composition_from_model(model, spec, complete_model=True)

            if not composition.is_refinement(connected_spec):
                if self.pid % 20 == 0:
                    print('.'),
                failed_spec = spec
                return False, composition, connected_spec,contract_inst, failed_spec

            print('+'),

        return True, composition, connected_spec,contract_inst, None


    def run(self):
        '''
        executes refinement check
        '''
        #import pdb
        #pdb.set_trace()
        #print 'thread %s running' % self.ident
        #return
        state, composition, connected_spec, contract_inst, failed_spec= \
            self.check_all_specs_threadsafe(self.model, z3_lock=self.z3_lock)

        if state:
            self.manager.result_queue.put(self.pid)
            self.found_event.set()
        else:
            self.manager.fail_queue.put(self.pid)
        #else:
        #    #check for consistency
        #    LOG.debug('pre consistency')
        #    constraints = self.z3_interface.check_for_consistency(self.model, self.candidates,
        #                                             contract_inst, connected_spec, z3_lock=self.z3_lock)

        #    if constraints:
        #        #add them to the constraint queue
        #        self.manager.constraint_queue.put(constraints)

        #we are done, release semaphore
        self.manager.semaphore.release()

        #LOG.debug('lock?')
        with self.manager.pool_lock:
            if not self.manager.terminate_event.is_set():
                self.manager.thread_pool.discard(self)

        #LOG.debug('done')


        return
