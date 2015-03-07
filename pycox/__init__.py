import logging

log = logging.getLogger()
log.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)

# create formatter and add it to the handlers
formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
ch.setFormatter(formatter)

# add the handlers to the logger
log.addHandler(ch)

log.debug('PYCOX INIT')
