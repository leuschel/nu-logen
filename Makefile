tests:
	sicstus -l examples/small_pe_tests.pl --goal "small_pe_tests:run_tests,halt."

test:
	sicstus -l examples/test_app.pl --goal "test(C),halt."

samples:
	sicstus -l examples/test_pe_sampler.pl