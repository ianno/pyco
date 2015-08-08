'''
This module manages the refinement checks using a set
of threads to speed things up

Author: Antonio Iannopollo
'''

from pycox import LOG
import threading
from Queue import Queue, Empty
import pycox.z3_interface
#import multiprocessing

MAX_THREADS = 8

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
        self.semaphore = threading.Semaphore(MAX_THREADS)
        self.found_refinement = threading.Event()

        self.composition = None
        self.connected_spec = None
        self.contract_inst = None
        self.model = None

        self.solution_lock = threading.Lock()
        self.z3_lock = threading.Lock()
        self.constraint_queue = Queue()

        self.thread_pool = set()
        self.pool_lock = threading.RLock()
        self.terminate_event = threading.Event()

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

    def synthesize(self, size_constraints):
        '''
        picks candidates and generates threads
        '''
        size = 1

        while True:
            try:
                with self.z3_lock:
                    model = self.z3_interface.propose_candidate()
            except pycox.z3_interface.NotSynthesizableError as err:
                if size < self.z3_interface.num_out:
                    LOG.debug('Synthesis for size %d failed. Increasing number of components...', size)
                    size = size + 1
                    self.solver.pop()
                    self.solver.push()
                    self.solver.add(size_constraints[size])
                else:
                    raise err
            else:
                #acquire semaphore
                self.semaphore.acquire()

                #check if event is successful
                if self.found_refinement.is_set():
                    #we are done. kill all running threads and exit
                    return self.terminate()

                #new refinement checker
                thread = RefinementChecker(model, self, self.found_refinement)
                #go
                thread.start()
                with self.pool_lock:
                    self.thread_pool.add(thread)

                #now reject the model, to get a new candidate
                LOG.debug('pre-lock')
                with self.z3_lock:
                    LOG.debug('pre-reject')
                    self.solver.add(self.z3_interface.reject_candidate(model))
                    LOG.debug('done')

                #try:
                #    composition, spec, contract_list = self.verify_candidate(model)
                #except NotSynthesizableError as err:
                #    LOG.debug("candidate not valid")
                #else:
                #    LOG.debug(model)
                #    for c in contract_list:
                #        LOG.debug(c)
                #    LOG.debug(composition)
                #    return model, composition, spec, contract_list

        #current_hierarchy = 0
        #c_list = self.candidate_list

        #LOG.debug('current hierarchy: %d' % current_hierarchy)

        #while True:
        #    try:
        #        #push current hierarchy level
        #        #pop is done in the finally clause
        #        LOG.debug('lock')
        #        with self.z3_lock:
        #            #LOG.debug('pre push')
        #            #self.solver.push()
        #            #LOG.debug('pre add hier')
        #            #self.solver.add(self.z3_interface.allow_hierarchy(current_hierarchy, c_list))
        #            LOG.debug('pre-propose')
        #            model = self.z3_interface.propose_candidate(self.size)
        #    except pycox.z3_interface.NotSynthesizableError as err:

        #        if current_hierarchy < self.z3_interface.max_hierarchy:
        #            LOG.debug('increase hierarchy to %d' % (current_hierarchy + 1))
        #            current_hierarchy += 1
        #        else:
        #            return self.terminate()

        #    else:

        #        #acquire semaphore
        #        self.semaphore.acquire()

        #        #check if event is successful
        #        if self.found_refinement.is_set():
        #            #we are done. kill all running threads and exit
        #            return self.terminate()

        #        #new refinement checker
        #        thread = RefinementChecker(model, c_list, self, self.found_refinement)
        #        #go
        #        thread.start()
        #        with self.pool_lock:
        #            self.thread_pool.add(thread)

        #        #now reject the model, to get a new candidate
        #        LOG.debug('pre-lock')
        #        with self.z3_lock:
        #            LOG.debug('pre-reject')
        #            self.solver.add(self.z3_interface.reject_candidate(model, c_list))
        #            LOG.debug('done')

        #        #empty queue with additional constraints
        #        while True:
        #            try:
        #                constraints = self.constraint_queue.get_nowait()
        #            except Empty:
        #                break
        #            else:
        #                LOG.debug('lock')
        #                with self.z3_lock:
        #                    LOG.debug('add %s' % constraints)
        #                    self.solver.add(constraints)
        #    finally:
        #        LOG.debug('lock')
        #        with self.z3_lock:
        #            #LOG.debug('pre-pop')
        #            #self.solver.pop()
        #            LOG.debug('popped')


    def terminate(self):
        '''
        close up nicely
        '''
        LOG.debug('terminating')
        #wait for all the threads to stop
        with self.pool_lock:
            self.terminate_event.set()

        for thread in self.thread_pool:
            thread.join()

        if self.found_refinement.is_set():
            return (self.model, self.composition, self.connected_spec, self.contract_inst)
        else:
            raise pycox.z3_interface.NotSynthesizableError()


class RefinementChecker(threading.Thread):
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
        self.result_queue = Queue()

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
                LOG.debug('ref check done 1')
                failed_spec = spec
                return False, composition, connected_spec,contract_inst, failed_spec

            LOG.debug('ref check done 2')

        return True, composition, connected_spec,contract_inst, None


    def run(self):
        '''
        executes refinement check
        '''
        #import pdb
        #pdb.set_trace()
        print 'thread %s running' % self.ident
        #return
        state, composition, connected_spec, contract_inst, failed_spec= \
            self.check_all_specs_threadsafe(self.model, z3_lock=self.z3_lock)

        if state:
            self.found_event.set()
            self.manager.set_successful_candidate(self.model, composition,
                                                  connected_spec, contract_inst)
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

        LOG.debug('lock?')
        with self.manager.pool_lock:
            if not self.manager.terminate_event.is_set():
                self.manager.thread_pool.discard(self)

        LOG.debug('done')


        return
