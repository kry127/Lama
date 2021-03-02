TESTS=$(sort $(basename $(wildcard test*.lama)))

RUNTIME_PATH=../../runtime
STDLIB_PATH=../../stdlib
LAMAC=../../src/lamac -tc -I $(STDLIB_PATH)

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@
	cat input/$@.input | LAMA=$(RUNTIME_PATH) $(LAMAC) -i $< > actual/$@.log && diff expected/$@.log actual/$@.log
	cat input/$@.input | LAMA=$(RUNTIME_PATH) $(LAMAC) -ds -s $< > actual/$@.log && diff expected/$@.log actual/$@.log
	LAMA=$(RUNTIME_PATH) $(LAMAC) $< && cat input/$@.input | ./$@ > actual/$@.log && diff expected/$@.log actual/$@.log

clean:
	$(RM) actual/test*.log *.s *.sm *~ $(TESTS) *.i
