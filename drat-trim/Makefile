install: compile test
	mkdir -p ../bin
	cp drat-trim ../bin/
test:
	./drat-trim ../examples/example1.cnf ../examples/example1.rup
compile:
	gcc -std=c99 -O2 -Wno-implicit-function-declaration -o drat-trim drat-trim.c
clean:
	rm -fv drat-trim
