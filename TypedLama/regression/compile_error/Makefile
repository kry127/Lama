TESTS=$(sort $(basename $(wildcard test*.lama)))

RUNTIME_PATH=../../../runtime
STDLIB_PATH=../../../stdlib
LAMAC=../../../src/lamac -tc -dp -I $(STDLIB_PATH)

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "Compilation error test: $@"
	rm -f "$(basename $<).html"
	! LAMA=$(RUNTIME_PATH) $(LAMAC) $<
	[ ! -f "$(basename $<).html" ] # lamac should not create any artifacts, .html dump are among of them

clean:
	$(RM) actual/test*.log test*.s test*.sm test*.html *~ $(TESTS) *.i
