export RUST_BACKTRACE=1
export RUST_LOG=ena::unify=INFO

default: ninja

all:
	ninja testbins-release testbins-debug -v
	@echo COMPLETE

ninja:
	cargo check
	cargo fmt
	cargo build
	python3 build.py
	#touch target/x86_64-unknown-linux-gnu/debug/parse
	ninja -v -k0 | tee out.log
	@echo COMPLETE

clean:
	cargo clean
	rm -rf build

bare:
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/bare.star -o build/bare

interp:
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/bare.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_local.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/recurse.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_recursive2.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_recursive.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/fix.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/loop.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/goto.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/dup_func.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_cond.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/monomorph.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/monomorph_static.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/star_args.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_float.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/nested_func.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/nested_func_return.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_global.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/nested_loops.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_ternary.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/static.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_static.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/static_var.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/nested_goto.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_args.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -v -i tests/bin/cps_mono.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_pass1.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_pass2.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_pass3.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_pass4.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_pass5.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_pass6.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/defer.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_cyclic.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/test_tuple.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- --interp -x -i tests/bin/cps_ret.star -o build/args3

run:
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/bare.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_local.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/recurse.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_recursive2.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -i tests/bin/test_recursive.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/fix.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/loop.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/goto.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/dup_func.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_cond.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/monomorph.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/monomorph_static.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -O -i tests/bin/star_args.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_float.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/nested_func.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -c -x -v -i tests/bin/nested_func_return.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_global.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/nested_loops.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_ternary.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/static.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_static.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/static_var.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/nested_goto.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_args.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_mono.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_pass1.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_pass2.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_pass3.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_pass4.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_pass5.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_pass6.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/defer.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_cyclic.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/test_tuple.star -o build/args3
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/cps_ret.star -o build/args3
	dot -Tpng build/args3.cont.dot -o cont.png

run2:
	cargo check
	python3 build.py
	touch target/x86_64-unknown-linux-gnu/debug/parse
	#RUST_LOG=INFO ninja -v static-debug-interp
	#RUST_LOG=INFO ninja -v static-debug-exe
	RUST_LOG=INFO ninja -v test_tuple

fmt:
	cargo fmt

.PHONY: examples
examples:
	clang-17 -c tests/prelude.c -o target/debug/prelude.o
	clang-17 -shared tests/prelude.c -o target/debug/prelude.so
	clang-17 -c examples/test.c -o target/debug/test.o
	clang-17 -S -emit-llvm examples/test.c -o target/debug/test.ll
	cat target/debug/test.ll
