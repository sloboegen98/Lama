TESTS=$(sort $(basename $(wildcard *.lama)))

LAMAC=../src/lamac

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	LAMA=../runtime 
	@echo "recursive: " && `which time` -f "$@\t%U" $(LAMAC) -s $^ < input
	@echo "byterun: " && \
		$(LAMAC) -b $^ && \
	 	`which time` -f "$@\t%U" ../byterun/interpreter $@.bc < input

clean:
	$(RM) test*.log *.s *.bc *~ $(TESTS) *.i
