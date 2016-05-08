default: tests.log

FLAGS = 
#--refinement-slicer

test:
	@../test.pl -c "../../../src/cbmc/cbmc $(FLAGS)"

tests.log: ../test.pl
	@../test.pl -c "../../../src/cbmc/cbmc $(FLAGS)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
