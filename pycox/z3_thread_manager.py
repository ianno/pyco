'''
This module manages the refinement checks using a set
of threads to speed things up

Author: Antonio Iannopollo
'''

from pycox import LOG
#import threading
#from Queue import Queue, Empty
from Queue import Empty
import pycox.z3_interface
import multiprocessing

MAX_THREADS = 8
WITH_COI = True

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
        self.rejection_queue = multiprocessing.Queue()

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
            except pycox.z3_interface.NotSynthesizableError as err:
                if size < self.z3_interface.max_components:
                    LOG.debug('Synthesis for size %d failed. Increasing number of components...', size)
                    size = size + 1
                    with self.z3_lock:
                        self.solver.pop()
                        self.solver.push()
                        self.solver.add(size_constraints[size])
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
                # while not self.fail_queue.empty():
                #     pid = self.fail_queue.get_nowait()
                #     self.model_dict.pop(pid)

                #new refinement checker
                thread = RefinementChecker(model, self, self.found_refinement, with_coi=WITH_COI)
                #go
                thread.start()
                with self.pool_lock:
                    self.model_dict[thread.pid] = model
                    self.thread_pool.add(thread)

                #now reject the model, to get a new candidate
                #LOG.debug('pre-lock')
                with self.z3_lock:
                    LOG.debug('pre-reject')
                    self.solver.add(self.z3_interface.reject_candidate(model))
                    LOG.debug('done')

                    #add additional constraints found by the runners
                    while not self.rejection_queue.empty():
                        (coi, i, unique_names_map, m_pid) = self.rejection_queue.get_nowait()
                        model = self.model_dict[m_pid]
                        LOG.debug(coi)
                        spec = self.z3_interface.specification_list[i]
                        # composition, connected_spec, contract_inst, unique_names_map = \
                        #     self.z3_interface.build_composition_from_model(model, spec, complete_model=True)
                        self.solver.add(self.z3_interface.reject_candidate(model, coi=coi, unique_names_map=unique_names_map))

                        #discard model
                        self.model_dict.pop(m_pid)

    def terminate(self):
        '''
        close up nicely
        '''
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
            raise pycox.z3_interface.NotSynthesizableError()

        self.model = self.model_dict[pid]

        #rebuild composition
        spec = self.z3_interface.specification_list[0]
        with self.z3_lock:
            self.composition, self.connected_spec, self.contract_inst, _ = \
                    self.z3_interface.build_composition_from_model(self.model, spec, complete_model=True)
        #wait for all the threads to stop


        #for thread in self.thread_pool:
        #    thread.join()

        return (self.model, self.composition, self.connected_spec, self.contract_inst)


class RefinementChecker(multiprocessing.Process):
    '''
    this thread executes a refinement checks and dies
    '''

    def __init__(self, model, manager, found_event, with_coi=False):
        '''
        instantiate
        '''
        self.model = model
        self.z3_interface = manager.z3_interface
        self.found_event = found_event
        self.manager = manager
        self.z3_lock = manager.z3_lock
        self.with_coi = with_coi
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
        for i in range(len(self.z3_interface.specification_list)):
            spec = self.z3_interface.specification_list[i]
            with z3_lock:
                composition, connected_spec, contract_inst, unique_names_map = \
                    self.z3_interface.build_composition_from_model(model, spec, complete_model=True)

            coi = composition.is_refinement(connected_spec, with_coi=self.with_coi)
            if coi is not True:
                LOG.debug('ref check done 1')
                failed_spec = spec

                #this is redundant, but it might exclude more contracts by using coi
                if self.with_coi:
                    # need to trim the last two characters in coi (because nuxmv checks a copy of the contracts)
                    coi = [elem[::-1].split('_', 1)[-1][::-1] for elem in coi]
                    self.manager.rejection_queue.put((coi, i, unique_names_map, self.pid))

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
