DIRS = ansi-c cbmc cpp goto-instrument goto-instrument-unwind \
       cbmc-incr-oneloop cbmc-incr cbmc-with-incr

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
