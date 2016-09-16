DIRS =  cbmc-incr-oneloop 
# array-refinement \
       cbmc-incr
#       cbmc cbmc-with-incr \
#       array-refinement-with-incr \

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
