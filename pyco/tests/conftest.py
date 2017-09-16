"""
Configuration file for pytest.

Author: Antonio Iannopollo
"""

def pytest_addoption(parser):
    parser.addoption("--lib2", action="store_true",
        help="redundancy level of the library.")
    parser.addoption("--lib3", action="store_true",
        help="redundancy level of the library.")
    parser.addoption("--lib4", action="store_true",
        help="redundancy level of the library.")
    parser.addoption("--nt", action="store_true",
        help="disable the use of types and user hints.")
    parser.addoption("--comps", action="store_true",
        help="minimize number of components.")
    parser.addoption("--ports", action="store_true",
        help="minimize number of ports.")
    parser.addoption("--out", action="store",
        help="output file name")
    parser.addoption("--plain", action="store_true",
        help="disable specification decomposition")

def pytest_generate_tests(metafunc):
    name = ''

    if 'library_redundancy' in metafunc.fixturenames:
        if metafunc.config.option.lib4:
            value = 4
        elif metafunc.config.option.lib3:
            value = 3
        else:
            value = 2

        name = name + "_library_redundancy-"+str(value)
        metafunc.parametrize("library_redundancy", [value])
    if 'no_types' in metafunc.fixturenames:
        if metafunc.config.option.nt:
            value = True
        else:
            value = False

        name = name + "_no_types-"+str(value)
        metafunc.parametrize("no_types", [value])
    if 'min_comps' in metafunc.fixturenames:
        if metafunc.config.option.comps:
            value = True
        else:
            value = False

        name = name + "_min_comps-"+str(value)
        metafunc.parametrize("min_comps", [value])
    if 'min_ports' in metafunc.fixturenames:
        if metafunc.config.option.ports:
            value = True
        else:
            value = False

        name = name + "_min_ports-"+str(value)
        metafunc.parametrize("min_ports", [value])

    #this must be called the last one
    if 'filename' in metafunc.fixturenames:
        name = metafunc.function.__name__ + name
        value = metafunc.config.getoption('--out', default=name)
        if value is None:
            value = name
        metafunc.parametrize("filename", [value])

    if 'plain' in metafunc.fixturenames:
        if metafunc.config.option.plain:
            value = True
        else:
            value = False

        name = name + "_plain-"+str(value)
        metafunc.parametrize("plain", [value])
