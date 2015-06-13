'''
example_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
Add reference

Author: Antonio Iannopollo
'''


from pycox.contract import Contract, BaseType
from pycox.library import (ContractLibrary, LibraryComponent,
                            LibraryPortMapping, LibraryCompositionMapping)
from pycox.synthesis import SynthesisInterface
from pycox import LOG

#let's start with types
class BreakableT(BaseType):
    '''
    an object that can break
    '''
    pass


class GeneratorT(BreakableT):
    '''
    generator type
    '''
    pass

class RectifierT(BreakableT):
    '''
    Rectifier
    '''
    pass

class ACLoadT(BaseType):
    '''
    AC load type
    '''
    pass

class ContactorT(BaseType):
    '''
    Generic Contactor
    '''
    pass

class ACContactorT(ContactorT):
    '''
    AC Contactor
    '''
    pass

class ACGenContactorT(ACContactorT):
    '''
    AC Generator Contactor
    '''
    pass

class ACBackContactorT(ACContactorT):
    '''
    AC Backup Contactor
    '''
    pass

class ACLoadContactorT(ACContactorT):
    '''
    AC Load Contactor
    '''
    pass

class DCContactorT(ContactorT):
    '''
    DC Contactor
    '''

class DCBackContactorT(DCContactorT):
    '''
    DC Backup Contactor
    '''

class DCLoadContactorT(DCContactorT):
    '''
    DC Load Contactor
    '''
class BusContactorT(ContactorT):
    '''
    Bus Contactor
    '''

class DCLoadT(BaseType):
    '''
    dc load type
    '''
    pass

#Now let's include some components
class AbstractGenerator(Contract):
    '''
    generator OK at beginning. Once broken stays broken.
    if fails eventually close the contactor
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACGenContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'G(fail -> F ! c)'

class DumbGenerator(Contract):
    '''
    Always open
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACGenContactorT)]
    ASSUMPTIONS = '!fail'
    GUARANTEES = 'G(! c)'

class StdGenerator(Contract):
    '''
    closes the contactor if everything is ok
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACGenContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'G(fail -> ! c) & G(!fail -> c)'

class SlowGenerator(Contract):
    '''
    closes the contactor if everything is ok.
    lock after 1 step
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACGenContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'c & G(fail -> X ! c) & G(!fail -> c)'

class ACSingleBackup(Contract):
    '''
    Backup between ac contactors
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT)]
    OUTPUT_PORTS = [('c', ACBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'
    GUARANTEES = 'G((fail1 | fail2) -> c) & G((!fail1 & !fail2) -> !c)'

class AC2WayBackup(Contract):
    '''
    Backup between ac contactors
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACBackContactorT), ('c2', ACBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'
    GUARANTEES = 'G((!fail1 & !fail2) -> (!c1 & !c2)) & \
                  G((fail1 & !fail2)-> (!c1 & !c2)) & \
                  G((!fail1 & fail2) -> (c1 & c2)) & \
                  G((fail1 & fail2) -> (!c1 & c2))'

class AC4WayBackup(Contract):
    '''
    Backup between ac contactors
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT),
                   ('fail3', GeneratorT), ('fail4', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACBackContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & !fail3 & !fail4 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2) &\
                   G(fail3 -> Xfail3) & G(fail4 -> Xfail4)'
    GUARANTEES = '''G(fail2 -> !c2) & G(fail3 -> !c3) &
                  G((!fail1 & !fail4) -> (!c1 & !c2 & !c3 & !c4)) &
                  G((!fail1 & !fail3 & fail4) -> (!c1 & !c2 & c3 & c4)) &
                  G((fail1 & !fail2 & !fail4) -> (c1 & c2 & !c3 & !c4)) &
                  G((!fail1 & !fail2 & fail3 & fail4) -> (!c1 & c2 & !c3 & c4)) &
                  G((fail1 & fail2 & !fail3 & !fail4) -> (c1 & !c2 & c3 & !c4)) &
                  G((fail2 & fail3 & (fail1 | fail4)) -> (c1 & !c2 & !c3 & c4))'''

class OneSideACLoad(Contract):
    '''
    Disconnect rectifier if it breaks
    '''
    INPUT_PORTS = [('ext_fail', RectifierT)]
    OUTPUT_PORTS = [('c', ACLoadContactorT)]

    ASSUMPTIONS = '!ext_fail'

    GUARANTEES = 'G(!ext_fail -> c) & \
                    G(ext_fail -> !c)'

class DCTwoSideTie(Contract):
    '''
    DC tie
    '''
    INPUT_PORTS = [('fail1', RectifierT), ('fail2', RectifierT)]
    OUTPUT_PORTS = [('c1', DCBackContactorT), ('c2', DCBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2'
    GUARANTEES = '''G((!fail1 & !fail2) -> (!c1 & !c2)) &
                    G((fail1 | fail2) -> (c1 & c2))'''

class DCLoadContactor(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('fail1', RectifierT), ('fail2', RectifierT)]
    OUTPUT_PORTS = [('c', DCLoadContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & G(!(fail1 & fail2))'
    GUARANTEES = 'G(c)'


#now add specs
#case A: 2gen-2contactors -> 4 ports
class GenIsolation1(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACContactorT), ('c2', ACContactorT)]
    #ASSUMPTIONS = '''!fail1 & !fail2 & G(!(fail1 & fail2)) &
    #                 G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'''
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) '''
    GUARANTEES = 'G(fail1 -> F!c1)'

class GenIsolation2(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACContactorT), ('c2', ACContactorT)]
    #ASSUMPTIONS = '''!fail1 & !fail2 & G(!(fail1 & fail2)) &
    #                 G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'''
    ASSUMPTIONS = '''!fail2 & G(fail2 -> Xfail2) '''
    GUARANTEES = 'G(fail2 -> F!c2)'


class GenIsolationBoth(Contract):
    '''
    generator 1 and 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACContactorT), ('c2', ACContactorT)]
    #ASSUMPTIONS = '''!fail1 & !fail2 & G(!(fail1 & fail2)) &
    #                 G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'''
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) '''
    GUARANTEES = 'G(fail1 -> F!c1) & G(fail2 -> F!c2)'


#case B: 4 generators, 6 contactors, only AC (3 components needed)
class GenIsolation1B(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT),
                   ('fail3', GeneratorT), ('fail4', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail1 -> F!c1)'

class GenIsolation2B(Contract):
    '''
    generator 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT),
                   ('fail3', GeneratorT), ('fail4', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail2 -> F!c2)'

class GenIsolation3B(Contract):
    '''
    generator 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT),
                   ('fail3', GeneratorT), ('fail4', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail3 -> F!c3)'

class GenIsolation4B(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT), ('fail2', GeneratorT),
                   ('fail3', GeneratorT), ('fail4', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail4 -> F!c4)'
