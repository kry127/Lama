.PHONY: regression

regression:
	make clean check -C compile_error
	make clean check -C runtime_error
	make clean check -C positive

clean:
	make clean -C compile_error
	make clean -C runtime_error
	make clean -C positive
