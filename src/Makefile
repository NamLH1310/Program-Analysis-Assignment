ANTLR_PATH := ANTLR_JAR=~/Downloads/antlr4-4.9.2-complete.jar

gen:
	$(ANTLR_PATH) python3 run.py gen

lexer_suite:
	$(ANTLR_PATH) python3 run.py test LexerSuite

parser_suite:
	$(ANTLR_PATH) python3 run.py test ParserSuite

pregen_suite:
	$(ANTLR_PATH) python3 run.py test PreGenSuite

vm_suite:
	python3 run.py test VMSuite
