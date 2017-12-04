'''
example_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
Add reference

Author: Antonio Iannopollo
'''


from pyco.contract import Contract, BaseType
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG

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

class ActiveGeneratorT(GeneratorT):
    '''
    active generator type
    '''
    pass

class BackupGeneratorT(GeneratorT):
    '''
    backup generator type
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
    INPUT_PORTS = [('fail', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c', ACGenContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'G(fail -> ! c) & G(!fail -> c)'

class SlowGenerator(Contract):
    '''
    closes the contactor if everything is ok.
    lock after 1 step
    '''
    INPUT_PORTS = [('fail', ActiveGeneratorT)]
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
    INPUT_PORTS = [('fail1', BackupGeneratorT), ('fail2', BackupGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'
    GUARANTEES = 'G((!fail1 & !fail2) -> (!c1 & !c2)) & \
                  G((fail1 & !fail2)-> (!c1 & !c2)) & \
                  G((!fail1 & fail2) -> (c1 & c2)) & \
                  G((fail1 & fail2) -> (!c1 & c2))'

class AC4WayBackup(Contract):
    '''
    Backup between ac contactors
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACBackContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & !fail3 & !fail4 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2) &\
                   G(fail3 -> Xfail3) & G(fail4 -> Xfail4)'
    GUARANTEES = '''G(fail2 -> !c2) & G(fail3 -> !c3) &
                    G(!(c2 & c3)) &
                  G((!fail1 & !fail4) -> (!c1 & !c2 & !c3 & !c4)) &
                  G((!fail1 & !fail3 & fail4) -> (!c1 & !c2 & c3 & c4)) &
                  G((fail1 & !fail2 & !fail4) -> (c1 & c2 & !c3 & !c4)) &
                  G((!fail1 & !fail2 & fail3 & fail4) -> (!c1 & c2 & !c3 & c4)) &
                  G((fail1 & fail2 & !fail3 & !fail4) -> (c1 & !c2 & c3 & !c4)) &
                  G((fail2 & fail3 & (fail1 | fail4)) -> (c1 & !c2 & !c3 & c4))'''

class AC4WayBackupAlt(Contract):
    '''
    Backup between ac contactors
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACBackContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & !fail3 & !fail4 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2) &\
                   G(fail3 -> Xfail3) & G(fail4 -> Xfail4)'
    GUARANTEES = '''G(fail -> !c1 & c3)'''

class ACBackupGen(Contract):
    '''
    Backup between ac contactors
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACBackContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACBackContactorT)]
    ASSUMPTIONS = '!fail1 & !fail2 & !fail3 & !fail4 & G(fail1 -> Xfail1) & G(fail2 -> Xfail2) &\
                   G(fail3 -> Xfail3) & G(fail4 -> Xfail4)'
    GUARANTEES = '''G(fail2 -> !c2) & G(fail3 -> !c3)'''

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
    ASSUMPTIONS = '!fail1 & !fail2'# & G(!(fail1 & fail2))'
    GUARANTEES = '''G(c)'''


#now add specs

#case 0: 1gen-2contactors -> 2 ports
class GenIsolation0(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACContactorT)]
    ASSUMPTIONS = '''!fail1  &
                     G(fail1 -> Xfail1)'''
    #ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) '''
    GUARANTEES = 'G(fail1 -> F!c1)'

#case A: 2gen-2contactors -> 4 ports
class GenIsolation1(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT)]
    ASSUMPTIONS = '''!fail1 & !fail2 & G(!(fail1 & fail2)) &
                     G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'''
    #ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) '''
    GUARANTEES = 'G(fail1 -> F!c1)'


class GenIsolation2(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT)]
    ASSUMPTIONS = '''!fail1 & !fail2 & G(!(fail1 & fail2)) &
                     G(fail1 -> Xfail1) & G(fail2 -> Xfail2)'''
    #ASSUMPTIONS = '''!fail2 & G(fail2 -> Xfail2) '''
    GUARANTEES = 'G(fail2 -> X!c2)'


#case A1: 4gen-2contactors -> 6 ports
class GenIsolation1_6(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2)'''
    GUARANTEES = 'c1 & G(fail1 -> X!c1)'

#case B: 4 generators, 6 contactors, only AC (3 components needed)
class GenIsolation1B(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'c1 & G(fail1 -> X!c1)'

class GenIsolation2B(Contract):
    '''
    generator 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail2 -> X!c2)'

class GenIsolation3B(Contract):
    '''
    generator 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail3 -> X!c3)'

class GenIsolation4B(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(fail4 -> X!c4)'

#test C: as per test B, but more specs
class NoShort(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G(!(c2 & c3))'

class NoParallelShort(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G((!fail1 & !fail4) -> F(!(c5 & c6)))'

class IsolateEmergencyBus(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4)'''
    GUARANTEES = 'G((!fail1 & !fail2 & ! fail3 & !fail4) -> F(!c2 & !c3 & !c5 & !c6))'



#case D -> include DC
class GenIsolation1D(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'c1 & G(fail1 -> X!c1)'

class GenIsolation2D(Contract):
    '''
    generator 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'G(fail2 -> X!c2)'

class GenIsolation3D(Contract):
    '''
    generator 2 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'G(fail3 -> X!c3)'

class GenIsolation4D(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'c4 & G(fail4 -> X!c4)'

class NoShortD(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'G(!(c2 & c3))'

class NoParallelShortD(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'G((!fail1 & !fail4) -> F(!(c5 & c6)))'

class IsolateEmergencyBusD(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''
    GUARANTEES = 'G((!fail1 & !fail2 & ! fail3 & !fail4) -> F(!c2 & !c3 & !c5 & !c6))'


class DCRightD(Contract):
    '''
    Right side of dc is always powered
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''

    GUARANTEES = 'G(!(fail_r1 & fail_r2) -> c10)'


class DCLeftD(Contract):
    '''
    Right side of dc is always powered
    '''
    INPUT_PORTS = [('fail1', ActiveGeneratorT), ('fail2', BackupGeneratorT),
                   ('fail3', BackupGeneratorT), ('fail4', ActiveGeneratorT),
                   ('fail_r1', RectifierT), ('fail_r2', RectifierT)]
    OUTPUT_PORTS = [('c1', ACGenContactorT), ('c2', ACGenContactorT),
                    ('c3', ACGenContactorT), ('c4', ACGenContactorT),
                    ('c6', ACBackContactorT), ('c5', ACBackContactorT),
                    ('c7', DCBackContactorT), ('c8', DCBackContactorT),
                    ('c9', DCLoadContactorT), ('c10', DCLoadContactorT)]
    ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) &
                     !fail2 & G(fail2 -> Xfail2) &
                     !fail3 & G(fail3 -> Xfail3) &
                     !fail4 & G(fail4 -> Xfail4) &
                     !fail_r1 & G(fail_r1 -> Xfail_r1) &
                     !fail_r2 & G(fail_r2 -> Xfail_r2)'''

    GUARANTEES = 'G(!(fail_r1 & fail_r2) -> c9)'
