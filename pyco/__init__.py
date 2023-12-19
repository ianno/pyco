import logging
import multiprocessing
import pdb

LOG = logging.getLogger('pyco')
LOG.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
#ch.setLevel(logging.DEBUG)

# create formatter and add it to the handlers
formatter = logging.Formatter('%(asctime)s  - %(process)d: %(filename)s:%(lineno)d - %(levelname)s - %(message)s')
ch.setFormatter(formatter)

# add the handlers to the logger
LOG.addHandler(ch)

# LOG.debug('PYCO INIT')

MAX_PROCESSES = multiprocessing.cpu_count()

#pdb.set_trace()
