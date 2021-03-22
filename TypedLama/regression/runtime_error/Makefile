TESTS=$(sort $(basename $(wildcard test*.lama)))

RUNTIME_PATH=../../../runtime
STDLIB_PATH=../../../stdlib
LAMAC=../../../src/lamac -tc -dp -I $(STDLIB_PATH)

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "Runtime error test: $@"
	cat input/$@.input | LAMA=$(RUNTIME_PATH) $(LAMAC) -i $< > actual/$@.log

clean:
	$(RM) actual/test*.log test*.s test*.sm test*.html *~ $(TESTS) *.i
