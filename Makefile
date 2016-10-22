SUBDIRS = c-checker drat-trim py-checker certified-checker ocaml-set-checker lingeling iglucose
install:
	for dir in $(SUBDIRS); do \
          $(MAKE) -C $$dir -f Makefile install; \
	done
clean:
	rm -rfv bin
	for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir -f Makefile clean; \
        done
