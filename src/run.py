import sys
import os
import subprocess
import unittest
from antlr4 import *

TARGET_DIR = '../target'
ANTLR_JAR  = os.environ.get('ANTLR_JAR')
GENERATE_DIR = 'main/crazy/parser'
G4FILE     ='main/crazy/parser/Cra2Pre.g4'

for path in ['./test/', TARGET_DIR+'/'+GENERATE_DIR]:
    sys.path.append(path)



def main(argv):
    if len(argv) < 1:
        printUsage()
    elif argv[0] == 'gen':
        subprocess.run(["java", "-jar", ANTLR_JAR, "-o", "../target",
                       "-no-listener", "-visitor", G4FILE])
    elif argv[0] == 'clean':
        subprocess.run(["rm", "-rf", TARGET_DIR + "/*"])

    elif argv[0] == 'test':
        if not os.path.isdir(TARGET_DIR + "/" + GENERATE_DIR):
            subprocess.run(["java", "-jar", ANTLR_JAR, "-o", GENERATE_DIR,
                           "-no-listener", "-visitor", G4FILE])
        if not (TARGET_DIR + "/" + GENERATE_DIR) in sys.path:
            sys.path.append(TARGET_DIR + "/" + GENERATE_DIR)
        if len(argv) < 2:
            printUsage()
        elif argv[1] == 'LexerSuite':
            from LexerSuite import LexerSuite
            getAndTest(LexerSuite)
        elif argv[1] =='ParserSuite':
            from ParserSuite import ParserSuite
            getAndTest(ParserSuite)
        elif argv[1] == 'PreGenSuite':
            from PreGenSuite import PreGenSuite
            getAndTest(PreGenSuite)
        elif argv[1] == 'VMSuite':
            from VMSuite import VMSuite
            getAndTest(VMSuite)
        else:
            printUsage()           
    else:
        printUsage()


def getAndTest(cls):
    suite = unittest.makeSuite(cls)
    test(suite)


def test(suite):
    from pprint import pprint
    from io import StringIO
    stream = StringIO()
    runner = unittest.TextTestRunner(stream=stream)
    result = runner.run(suite)
    print('Tests run ', result.testsRun)
    print('Errors ', result.errors)
    pprint(result.failures)
    stream.seek(0)
    print('Test output\n', stream.read())


def printUsage():
    print("python3 run.py gen")
    print("python3 run.py test LexerSuite")
    print("python3 run.py test ParserSuite")
    print("python3 run.py test PreGenSuite")
    print("python3 run.py test VMSuite")


if __name__ == "__main__":
    main(sys.argv[1:])
