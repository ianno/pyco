'''
This module manages the refinement checks using a set
of threads to speed things up

Author: Antonio Iannopollo
'''

from pycox import LOG
import threading
from Queue import Queue, Empty
import pycox.z3_interface
import multiprocessing

MAX_THREADS = 8

def check_refinement_in_process(queue):
    '''
    check refinement and write the result in queue
    '''
    LOG.debug('reading')
    item = queue.get()
    LOG.debug('read')
    result = concrete.is_refinement(abstract)
    queue.put(result)

    return


class ModelVerificationManager(object):
    '''
    manages refinement threads
    '''

    def __init__(self, z3_interface, size, candidate_list):
        '''
        set up solver and thread status
        '''

        self.solver = z3_interface.solver
        self.z3_interface = z3_interface
        self.semaphore = threading.Semaphore(MAX_THREADS)
        self.found_refinement = threading.Event()

        self.candidate_list = candidate_list
        self.size = size

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

    def synthesize(self):
        '''
        picks candidates and generates threads
        '''

        current_hierarchy = 0
        c_list = self.candidate_list

        LOG.debug('current hierarchy: %d' % current_hierarchy)

        while True:
            try:
                #push current hierarchy level
                #pop is done in the finally clause
                LOG.debug('lock')
                with self.z3_lock:
                    LOG.debug('pre push')
                    self.solver.push()
                    LOG.debug('pre add hier')
                    self.solver.add(self.z3_interface.allow_hierarchy(current_hierarchy, c_list))
                    LOG.debug('pre-propose')
                    model = self.z3_interface.propose_candidate(self.size)
            except pycox.z3_interface.NotSynthesizableError as err:

                if current_hierarchy < self.z3_interface.max_hierarchy:
                    LOG.debug('increase hierarchy to %d' % (current_hierarchy + 1))
                    current_hierarchy += 1
                else:
                    return self.terminate()

            else:

                #acquire semaphore
                self.semaphore.acquire()

                #check if event is successful
                if self.found_refinement.is_set():
                    #we are done. kill all running threads and exit
                    return self.terminate()

                #new refinement checker
                thread = RefinementChecker(model, c_list, self, self.found_refinement)
                #go
                thread.start()
                with self.pool_lock:
                    self.thread_pool.add(thread)

                #now reject the model, to get a new candidate
                with self.z3_lock:
                    self.solver.add(self.z3_interface.reject_candidate(model, c_list))

                #empty queue with additional constraints
                while True:
                    try:
                        constraints = self.constraint_queue.get_nowait()
                    except Empty:
                        break
                    else:
                        with self.z3_lock:
                            self.solver.add(constraints)
            finally:
                LOG.debug('lock')
                with self.z3_lock:
                    LOG.debug('pre-pop')
                    self.solver.pop()
                    LOG.debug('popped')


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

    def __init__(self, model, candidates, manager, found_event):
        '''
        instantiate
        '''
        self.model = model
        self.candidates = candidates
        self.z3_interface = manager.z3_interface
        self.found_event = found_event
        self.manager = manager
        self.z3_lock = manager.z3_lock
        self.result_queue = multiprocessing.Queue()

        super(RefinementChecker, self).__init__()


    def check_all_specs_threadsafe(self, model, candidates, z3_lock):
        '''
        check if the model satisfies a number of specs, if provided
        '''
        composition = None
        connected_spec = None
        contract_inst = None
        for spec in self.z3_interface.specification_list:
            with z3_lock:
                composition, connected_spec, contract_inst = \
                    self.z3_interface.build_composition_from_model(model, spec,
                                                                   candidates,
                                                                   complete_model=False)

            #LOG.debug('start process')
            #process = multiprocessing.Process(target=check_refinement_in_process,
            #                        args=((self.result_queue, )))
            #
            #process.start()

            #LOG.debug('send contracts')
            #self.result_queue.put([composition, connected_spec])
            #is_refinement = self.result_queue.get()

            #LOG.debug('got results!!')


            #if not is_refinement:
            if not composition.is_refinement(connected_spec):
                return (False, composition, connected_spec, contract_inst)

        return (True, composition, connected_spec, contract_inst)

    def run(self):
        '''
        executes refinement check
        '''
        #import pdb
        #pdb.set_trace()
        print 'thread %s running' % self.ident
        #return
        state, composition, connected_spec, contract_inst = \
            self.check_all_specs_threadsafe(self.model, self.candidates, z3_lock=self.z3_lock)

        if state:
            self.found_event.set()
            self.manager.set_successful_candidate(self.model, composition,
                                                  connected_spec, contract_inst)
        else:
            #check for consistency
            constraints = self.z3_interface.check_for_consistency(self.model, self.candidates,
                                                     contract_inst, connected_spec, z3_lock=self.z3_lock)

            if constraints:
                #add them to the constraint queue
                self.manager.constraint_queue.put(constraints)

        #we are done, release semaphore
        self.manager.semaphore.release()

        LOG.debug('lock?')
        with self.manager.pool_lock:
            if not self.manager.terminate_event.is_set():
                self.manager.thread_pool.discard(self)

        LOG.debug('done')


        return
