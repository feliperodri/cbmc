default: tests.log

include ../../src/config.inc

test:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation"
ifeq ($(filter %DBDD_GUARDS, $(CXXFLAGS)),)
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading
else
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -X bdd-expected-timeout -s symex-driven-loading
endif

tests.log: ../$(CPROVER_DIR)/regression/test.pl
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation"
ifeq ($(filter %DBDD_GUARDS, $(CXXFLAGS)),)
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading
else
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -X bdd-expected-timeout -s symex-driven-loading
endif

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log tests-symex-driven-loading.log

%.class: %.java ../../src/org.cprover.jar
	javac -g -cp ../../src/org.cprover.jar:. $<

nondet_java_files := $(shell find . -name "Nondet*.java")
nondet_class_files := $(patsubst %.java, %.class, $(nondet_java_files))

.PHONY: nondet-class-files
nondet-class-files: $(nondet_class_files)

.PHONY: clean-nondet-class-files
clean-nondet-class-files:
	-rm $(nondet_class_files)
