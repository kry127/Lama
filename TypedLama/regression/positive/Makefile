TESTS=$(sort $(basename $(wildcard test*.lama)))

RUNTIME_PATH=../../../runtime
STDLIB_PATH=../../../stdlib
LAMAC=../../../src/lamac -tc -dp -I $(STDLIB_PATH)

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "Type positive test: $@"
	cat input/$@.input | LAMA=$(RUNTIME_PATH) $(LAMAC) -i $< > actual/$@.log && diff expected/$@.log actual/$@.log
	# TODO make cast for stack representation
	#cat input/$@.input | LAMA=$(RUNTIME_PATH) $(LAMAC) -ds -s $< > actual/$@.log && diff expected/$@.log actual/$@.log
	#LAMA=$(RUNTIME_PATH) $(LAMAC) $< && cat input/$@.input | ./$@ > actual/$@.log && diff expected/$@.log actual/$@.log

clean:
	$(RM) actual/test*.log test*.s test*.sm test*.html *~ $(TESTS) *.i
