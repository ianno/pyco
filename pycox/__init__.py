import logging

LOG = logging.getLogger('pycox')
LOG.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
#ch.setLevel(logging.DEBUG)

# create formatter and add it to the handlers
formatter = logging.Formatter('%(asctime)s  - %(filename)s:%(lineno)d - %(levelname)s - %(message)s')
ch.setFormatter(formatter)

# add the handlers to the logger
LOG.addHandler(ch)

LOG.debug('PYCOX INIT')
