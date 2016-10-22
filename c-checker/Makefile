install: compile test
	mkdir -p ../bin
	cp c-checker ../bin/
compile:
	gcc -std=c99 -O2 -o c-checker c-checker.c
test:
	./c-checker ../examples/example1.grit
clean:
	rm -fv c-checker
