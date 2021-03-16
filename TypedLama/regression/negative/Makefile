TESTS=$(sort $(basename $(wildcard test*.lama)))

RUNTIME_PATH=../../../runtime
STDLIB_PATH=../../../stdlib
LAMAC=../../../src/lamac -tc -I $(STDLIB_PATH)

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "Type negative test: $@"
	! LAMA=$(RUNTIME_PATH) $(LAMAC) $<

clean:
	$(RM) actual/test*.log test*.s test*.sm test*.html *~ $(TESTS) *.i
