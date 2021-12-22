TESTS=$(sort $(basename $(wildcard test*.lama)))

LAMAC=../src/lamac
BYINT=../byterun/interpreter

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@
#	cat $@.input | LAMA=../runtime $(LAMAC) -i $< > $@.log && diff $@.log orig/$@.log
#	cat $@.input | LAMA=../runtime $(LAMAC) -ds -s $< > $@.log && diff $@.log orig/$@.log
#	LAMA=../runtime $(LAMAC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log
	$(LAMAC) -b $< && cat $@.input | $(BYINT) $@.bc > $@.log && diff $@.log orig/$@.log

clean:
	$(RM) test*.log *.s *~ $(TESTS) *.i
	$(RM) *.bc
	$(MAKE) clean -C expressions
	$(MAKE) clean -C deep-expressions
