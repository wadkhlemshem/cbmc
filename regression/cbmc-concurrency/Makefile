default: tests.log

test:
	@../test.pl -c "../../../src/cbmc/cbmc --lazy-encoding"
#	@../test.pl -c ../../../src/cbmc/cbmc
#	@../test.pl -c "../../../src/cbmc/cbmc-mus2 --lazy-encoding"
#	@../test.pl -c "../../../src/cbmc/cbmc-mus --lazy-encoding"
#	@../test.pl -c $W/svncprover/releases/cbmc-5.1/src/cbmc/cbmc
#	@../test.pl -c $W/svncprover/trunk5359/src/cbmc/cbmc

tests.log: ../test.pl
	@../test.pl -c ../../../src/cbmc/cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
